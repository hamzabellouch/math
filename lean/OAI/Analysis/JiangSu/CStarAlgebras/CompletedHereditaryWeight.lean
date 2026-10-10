import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Hereditary
import OAI.Analysis.JiangSu.Nonunital.NonUnitalHereditaryBridge

namespace OAI

section

noncomputable section
namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_contraction_square_le {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (e : D) (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e * e ≤ e := by
  have hb := CStarAlgebra.star_left_conjugate_le_norm_smul
    (a := CFC.sqrt e) (b := e) he.isSelfAdjoint
  rw [(CFC.sqrt_nonneg e).star_eq, CFC.sqrt_mul_sqrt_self e he] at hb
  have hid : CFC.sqrt e * e * CFC.sqrt e = e * e := by
    calc
      _ = CFC.sqrt e * (CFC.sqrt e * CFC.sqrt e) * CFC.sqrt e := by
        rw [CFC.sqrt_mul_sqrt_self e he]
      _ = (CFC.sqrt e * CFC.sqrt e) * (CFC.sqrt e * CFC.sqrt e) := by simp only [mul_assoc]
      _ = e * e := by rw [CFC.sqrt_mul_sqrt_self e he]
  rw [hid] at hb
  exact hb.trans (by simpa only [one_smul] using smul_le_smul_of_nonneg_right he1 he)

theorem completedWeight_le_rank_of_hereditary (τ : TracialState A) (h c : CornerCompletion A)
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hc1 : ‖c‖ ≤ 1)
    (hcm : (c : Unitization ℂ (CornerCompletion A)) ∈
      hereditaryCarrier (h : Unitization ℂ (CornerCompletion A))) :
    completedDiagonalWeight τ c ≤ completedRootRank τ h := by
  have hsm : ((CFC.sqrt c : CornerCompletion A) : Unitization ℂ (CornerCompletion A)) ∈
      hereditaryCarrier (h : Unitization ℂ (CornerCompletion A)) := by
    rw [← Unitization.sqrt_inr]
    exact hereditary_sqrt_mem (Unitization.inr_nonneg_iff.mpr hh)
      (Unitization.inr_nonneg_iff.mpr hc) hcm
  have ht := nonUnitalRoot_mul_hereditary_tendsto h (CFC.sqrt c) hh hsm
  have ht' := ht.mul ht.star
  have hlim : CFC.sqrt c * star (CFC.sqrt c) = c := by
    rw [(CFC.sqrt_nonneg c).star_eq, CFC.sqrt_mul_sqrt_self c hc]
  rw [hlim] at ht'
  apply completedDiagonalWeight_le_of_tendsto τ ht'
  intro j
  have he := nonUnitalRoot_nonneg h j
  have hid : (nonUnitalRoot h j * CFC.sqrt c) * star (nonUnitalRoot h j * CFC.sqrt c) =
      star (nonUnitalRoot h j) * c * nonUnitalRoot h j := by
    rw [star_mul, (CFC.sqrt_nonneg c).star_eq, he.star_eq]
    simp only [mul_assoc, ← mul_assoc (CFC.sqrt c) (CFC.sqrt c), CFC.sqrt_mul_sqrt_self c hc]
  rw [hid]
  apply (completedDiagonalWeight_mono τ ?_).trans (le_iSup (fun j =>
    completedDiagonalWeight τ (nonUnitalRoot h j)) j)
  calc
    _ ≤ ‖c‖ • (star (nonUnitalRoot h j) * nonUnitalRoot h j) :=
      CStarAlgebra.star_left_conjugate_le_norm_smul (nonUnitalRoot h j) c hc.isSelfAdjoint
    _ ≤ 1 • (star (nonUnitalRoot h j) * nonUnitalRoot h j) :=
      smul_le_smul_of_nonneg_right hc1 (star_mul_self_nonneg _)
    _ = nonUnitalRoot h j * nonUnitalRoot h j := by rw [one_smul, he.star_eq]
    _ ≤ nonUnitalRoot h j := positive_contraction_square_le _ he (nonUnitalRoot_norm_le h hh j)

end Pureness

end
end

end OAI
