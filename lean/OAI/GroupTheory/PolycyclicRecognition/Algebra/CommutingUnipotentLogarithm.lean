import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import Mathlib.Algebra.Polynomial.Smeval

namespace OAI

/-! # The logarithm of commuting unipotent products -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem commute_nilpotentLog {a b : A} (h : Commute a b) :
    Commute (nilpotentLog a) (nilpotentLog b) := by
  unfold nilpotentLog finiteNilpotentLog
  simp only [Polynomial.aeval_eq_smeval]
  exact Polynomial.smeval_commute ℚ _ _ h

theorem nilpotentLog_unipotent_mul {a b : A} (h : Commute a b)
    (ha : IsNilpotent a) (hb : IsNilpotent b) :
    nilpotentLog ((1 + a) * (1 + b) - 1) = nilpotentLog a + nilpotentLog b := by
  have hc := commute_nilpotentLog h
  have hn := hc.isNilpotent_add (nilpotentLog_nilpotent a ha) (nilpotentLog_nilpotent b hb)
  have he : IsNilpotent.exp (nilpotentLog a + nilpotentLog b) = (1 + a) * (1 + b) := by
    rw [IsNilpotent.exp_add_of_commute hc (nilpotentLog_nilpotent a ha)
      (nilpotentLog_nilpotent b hb), exp_nilpotentLog a ha, exp_nilpotentLog b hb]
  rw [← he, nilpotentLog_exp _ hn]

end PolycyclicRecognition

end

end OAI
