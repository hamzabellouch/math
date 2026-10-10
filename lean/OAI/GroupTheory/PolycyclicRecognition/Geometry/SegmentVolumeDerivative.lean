import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! # Differentiating the segment-volume inequality -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter Metric
open scoped Topology

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- Differentiability controls the whole short one-sided segment, so the
segment-volume lower bound passes to its derivative without any extra
Hausdorff-convergence hypothesis. -/
theorem le_segmentSupport_derivative
    (f : ℝ → W) (hf : Continuous f) (w : W) (hderiv : HasDerivAt f w 0)
    (p : ℝ) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hvolume : ∀ T : ℝ, 0 < T → T < T₀ → T * p ≤ D.templateSupport (f '' Icc 0 T)) :
    p ≤ D.segmentSupport w := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (D.templateSupportConstant + 1)
  have hε : 0 < ε := div_pos hη (by linarith [D.templateSupportConstant_nonneg])
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp (hderiv.isLittleO.def hε)
  let T := min (δ / 2) (T₀ / 2)
  have hT : 0 < T := lt_min (half_pos hδ) (half_pos hT₀)
  have hTδ : T < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hTT₀ : T < T₀ := (min_le_right _ _).trans_lt (half_lt_self hT₀)
  let E := (fun z : W => z + f 0) '' segment ℝ 0 (T • w)
  have hseg : IsCompact (segment ℝ (0 : W) (T • w)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hsegne : (segment ℝ (0 : W) (T • w)).Nonempty := by
    rw [segment_eq_image]
    exact (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _
  have hE : IsCompact E := hseg.image (continuous_id.add_const (f 0))
  have hnear : ∀ x ∈ f '' Icc 0 T, ∃ y ∈ E, ‖x - y‖ ≤ ε * T := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨t • w + f 0, ⟨t • w, ?_, rfl⟩, ?_⟩
    · rw [segment_eq_image]
      refine ⟨t / T, ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩, ?_⟩
      simp only [smul_zero, zero_add, smul_smul]
      rw [div_mul_cancel₀ _ hT.ne']
    · have htδ : dist t 0 < δ := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact ht.2.trans_lt hTδ
      have hh := hsmall htδ
      simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
      have he : f t - (t • w + f 0) = f t - f 0 - t • w := by abel
      rw [he]
      exact hh.trans (mul_le_mul_of_nonneg_left ht.2 hε.le)
  have hnonempty : (f '' Icc (0 : ℝ) T).Nonempty :=
    (nonempty_Icc.mpr hT.le).image f
  have hbound := D.templateSupport_le_of_nearby (isCompact_Icc.image hf) hnonempty
    hE (mul_nonneg hε.le hT.le) hnear
  have htarget : D.templateSupport E = T * D.segmentSupport w := by
    rw [D.templateSupport_translate hseg hsegne (f 0),
      D.templateSupport_segment, D.segmentSupport_smul_of_nonneg w hT.le]
  rw [htarget] at hbound
  have hscaled := (hvolume T hT hTT₀).trans hbound
  have hdivide : p ≤ D.segmentSupport w + D.templateSupportConstant * ε := by
    apply (mul_le_mul_iff_right₀ hT).mp
    nlinarith
  apply hdivide.trans
  apply add_le_add le_rfl
  dsimp [ε]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by linarith [D.templateSupportConstant_nonneg])).mpr
  nlinarith [D.templateSupportConstant_nonneg]

end PolycyclicRecognition.SupportDatum

end

end OAI
