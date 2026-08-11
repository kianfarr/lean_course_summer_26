import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic --def of π
import Mathlib.Analysis.Complex.Trigonometric -- def of trig fns
import Mathlib.NumberTheory.Real.Irrational -- def irrationality
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs -- def higher order derivatives
import LectureNotes.lecture9.examples9 -- integral definition
import Mathlib.Analysis.Calculus.Deriv.Basic -- deriv definition

set_option linter.style.longLine false

variable {a b : ℤ} {n : ℕ}

noncomputable def f (a b : ℤ) : ℕ → (ℝ → ℝ) := fun n ↦ (fun x ↦ x^n*(a-b*x)^n/(n.factorial))

noncomputable def F (a b : ℤ) : ℕ → (ℝ → ℝ) := fun n ↦ (∑ i ∈ Finset.range (n + 1), (iteratedDeriv (2*i) (f a b n)))

lemma zeroLessThanPi : 0 < Real.pi := by
  exact Real.pi_pos

lemma integral_fsin : MyRiemannIntegral.riemannIntegral ((f a b n) * Real.sin) Real.pi_pos = (F a b n Real.pi) + (F a b n 0) := by
  calc
    MyRiemannIntegral.riemannIntegral ((f a b n) * Real.sin) Real.pi_pos = (deriv F)
