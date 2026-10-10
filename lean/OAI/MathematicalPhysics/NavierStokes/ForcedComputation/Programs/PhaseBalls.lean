import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FastVectorArithmetic

namespace OAI

/-! Rational balls for the finite derivative recurrence of the logarithmic
clock. No modulus for a derivative of the slowed field is assumed. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def phaseBalls (r : ℕ) (a : ℕ → ℕ → Fin 3 → QBall) :
    ℕ → ℕ → ℕ → Fin 3 → QBall
  | 0, k => a k
  | n + 1, k => fun N j =>
      (phaseBalls r a n (k + 1) N j).add
        ((QBall.exact (-(r + n : ℚ))).mul (phaseBalls r a n k N j))

theorem phaseBalls_contains (r : ℕ) {A : ℝ → Space} (hA : ContDiff ℝ ∞ A)
    (s : ℝ) {a : ℕ → ℕ → Fin 3 → QBall}
    (ha : ∀ k N j, (a k N j).Contains (iteratedDeriv k A s j))
    (n k N : ℕ) (j : Fin 3) :
    (phaseBalls r a n k N j).Contains (iteratedDeriv k (phaseIter r A n) s j) := by
  induction n generalizing k with
  | zero => exact ha k N j
  | succ n ih =>
    rw [show phaseIter r A (n + 1) =
      phaseDerivative (r + n) (phaseIter r A n) from rfl,
      iteratedDeriv_phaseDerivative (r + n) k (phaseIter_smooth r hA n)]
    have h := QBall.contains_add (ih (k + 1))
      (QBall.contains_mul (QBall.contains_exact (-(r + n : ℚ))) (ih k))
    simpa only [phaseBalls, Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Nat.cast_add,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, neg_mul] using h

theorem phaseBalls_converges (r : ℕ) {A : ℝ → Space} (hA : ContDiff ℝ ∞ A)
    (s : ℝ) {a : ℕ → ℕ → Fin 3 → QBall}
    (ha : ∀ k j, QBall.Converges (fun N => a k N j) (iteratedDeriv k A s j))
    (n k : ℕ) (j : Fin 3) :
    QBall.Converges (fun N => phaseBalls r a n k N j)
      (iteratedDeriv k (phaseIter r A n) s j) := by
  induction n generalizing k with
  | zero => exact ha k j
  | succ n ih =>
    rw [show phaseIter r A (n + 1) =
      phaseDerivative (r + n) (phaseIter r A n) from rfl,
      iteratedDeriv_phaseDerivative (r + n) k (phaseIter_smooth r hA n)]
    have h := (ih (k + 1)).add
      ((QBall.converges_exact (-(r + n : ℚ))).mul (ih k))
    simpa only [phaseBalls, Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Nat.cast_add,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, neg_mul] using h

end ForcedComputation

end OAI
