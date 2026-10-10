import OAI.Analysis.CircleDomains.Modulus.TerminalNormBudget
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! The distinct labels of physical terminals charge each original band
at most once in the finite oscillation estimate. -/

open Function

namespace CircleDomainRigidity

theorem finite_label_band_norm_le {I S : Type*} [Fintype I]
    (label : I → S) (hinj : Injective label) (b : S → ℝ)
    (hb : Summable (fun s => b s ^ 2)) :
    Real.sqrt (∑ i, b (label i) ^ 2) ≤ Real.sqrt (∑' s, b s ^ 2) := by
  classical
  apply Real.sqrt_le_sqrt
  have heq : (∑ s ∈ Finset.univ.image label, b s ^ 2) = ∑ i, b (label i) ^ 2 :=
    Finset.sum_image (fun i _ j _ hij => hinj hij)
  rw [← heq]
  exact hb.sum_le_tsum _ (fun s _ => sq_nonneg (b s))

end CircleDomainRigidity

end OAI
