import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic --def of π
import Mathlib.Analysis.Complex.Trigonometric -- def of trig fns
import Mathlib.NumberTheory.Real.Irrational -- def irrationality
import LectureNotes.lecture9.examples9
import LectureNotes.lecture8.examples8

set_option linter.style.longLine false

variable {a b : ℤ} {n : ℕ}

noncomputable def f : ℕ → (ℝ → ℝ) := fun n ↦ (fun x ↦ x^n*(a-b*x)^n/(n.factorial))

def iteratedDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  | 0 => g

noncomputable def F : ℕ → (ℝ → ℝ) := fun n ↦ (∑ i ∈ Finset.range (n + 1), (iteratedDeriv (2*i) (f n)))

lemma integral_fsin : MyRiemannIntegral.riemannIntegral ((f n) * Real.sin) Real.pi_pos = (F n Real.pi) + (F n 0) := by
  calc
    MyRiemannIntegral.riemannIntegral ((f n) * Real.sin) Real.pi_pos = (deriv F)
