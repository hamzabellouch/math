import OAI.Probability.InvariantIsing.Gaussian.GaussianClippedStieltjes

namespace OAI

/-! The literal MP law is fixed by clipping to its nonnegative support interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma marchenkoPastur_mem_nonnegative_interval {α : ℝ} (hα : 0 < α) :
    ∀ᵐ x ∂marchenkoPasturMeasure α, x ∈ Icc (0 : ℝ) (marchenkoPasturB α) := by
  have := marchenkoPastur_probability hα
  filter_upwards [(marchenkoPasturMeasure α).support_mem_ae] with x hx
  have hb := marchenkoPastur_support_bound hα hx
  exact ⟨(mp_lower_nonneg hα.le).trans hb.1,hb.2⟩

lemma marchenkoPastur_clipped_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (∫ x, positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x)
      ∂marchenkoPasturMeasure α) = marchenkoPasturTransform t α := by
  calc
    _ = ∫ x, positiveResolventTest t x ∂marchenkoPasturMeasure α := by
      apply integral_congr_ae
      filter_upwards [marchenkoPastur_mem_nonnegative_interval hα] with x hx
      rw [spectralClip_eq hx]
    _ = _ := marchenkoPastur_transform hα ht

end InvariantIsing

end

end OAI
