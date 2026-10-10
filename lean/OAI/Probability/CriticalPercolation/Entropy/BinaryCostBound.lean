import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryConfiguration

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
local instance costBoundFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma constructionCost_le {c : ℝ} (hc : 0<c)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : (8:ℝ)^(-(n:ℤ)) ≤ descriptorMass G order d x p w s n D) :
    constructionCost G order d x p w c s n D ≤
      Real.log (1/prob w (endpointEvent G (x 0) (x d) s)) + n*(Real.log 8+Real.log (1/c)) := by
  have ho : 0 < descriptorMass G order d x p w s n D :=
    (zpow_pos (by norm_num : (0:ℝ)<8) _).trans_le hD
  have hl := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<8) _) hD
  rw [Real.log_zpow] at hl
  simp only [Int.cast_neg,Int.cast_natCast] at hl
  unfold constructionCost
  rw [Real.log_div (mul_ne_zero (inv_ne_zero hδ.ne') (pow_ne_zero _ (inv_ne_zero hc.ne'))) ho.ne',
    Real.log_mul (inv_ne_zero hδ.ne') (pow_ne_zero _ (inv_ne_zero hc.ne')),Real.log_pow]
  simp only [one_div]
  nlinarith

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
