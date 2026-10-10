import OAI.Analysis.CircleDomains.Sobolev.LipschitzLengthFiberMajorant
import OAI.Analysis.CircleDomains.Topology.PlaneCriticalFibers

namespace OAI

/-! Null planar sets meet almost every fiber of a Lipschitz scalar map
in a set of zero one-dimensional Hausdorff measure. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planar_hausdorff_two_zero_of_volume_zero {A : Set ℂ} (hA : volume A = 0) :
    (μH[2] : Measure ℂ) A = 0 := by
  have h := Complex.antilipschitz_equivRealProd.le_hausdorffMeasure_image
    (by norm_num : (0 : ℝ) ≤ 2) A
  rw [hausdorffMeasure_prod_real] at h
  have he : volume (Complex.measurableEquivRealProd '' A) = volume A := by
    rw [← Complex.volume_preserving_equiv_real_prod.map_eq,
      Complex.measurableEquivRealProd.map_apply,
      Complex.measurableEquivRealProd.injective.preimage_image]
  change volume (Complex.equivRealProd '' A) = volume A at he
  exact le_antisymm (by simpa only [he, hA, mul_zero] using h) bot_le

lemma lipschitz_null_fibers {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {A : Set ℂ} (hA : volume A = 0) :
    ∀ᵐ t, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {t}) = 0 := by
  have hz := planar_hausdorff_two_zero_of_volume_zero hA
  obtain ⟨G,hG,hbound,hint⟩ := exists_exact_lipschitz_length_fiber_majorant A
    (by rw [hz]; exact ENNReal.zero_lt_top) L f hf
  rw [hz, mul_zero] at hint
  have he : (∫⁻ t, G t) = 0 := le_antisymm hint bot_le
  filter_upwards [(lintegral_eq_zero_iff hG).mp he] with t ht
  exact le_antisymm ((hbound t).trans_eq ht) bot_le

end CircleDomainRigidity

end

end OAI
