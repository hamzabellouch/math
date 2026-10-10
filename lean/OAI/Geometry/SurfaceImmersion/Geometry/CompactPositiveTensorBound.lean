import OAI.Geometry.SurfaceImmersion.Atlas.MetricReadBounds

namespace OAI

/-! A compact family of positive surface tensors has one quadratic lower
bound in the fixed coordinate norm. -/
noncomputable section
open Set Metric
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma evaluate_smul_both (H : Tensor) (c : ℝ) (v : Base) :
    evaluate H (c • v) (c • v) = c^2*evaluate H v v := by
  simp only [evaluate,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem compact_positive_tensor_lower_bound {T : Set Tensor} (hT : IsCompact T)
    (hpos : ∀ H ∈ T, ∀ v : Base, v ≠ 0 → 0 < evaluate H v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ H ∈ T, ∀ v : Base, c*‖v‖^2 ≤ evaluate H v v := by
  let K : Set (Tensor × Base) := T ×ˢ sphere 0 1
  have hK : IsCompact K := hT.prod (isCompact_sphere 0 1)
  have hf : Continuous (fun z : Tensor × Base => evaluate z.1 z.2 z.2) := by
    unfold evaluate
    fun_prop
  have hp : ∀ z ∈ K, 0 < evaluate z.1 z.2 z.2 := by
    rintro ⟨H,v⟩ ⟨hH,hv⟩
    apply hpos H hH v
    intro hz
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨c,hc,hb⟩ := hK.exists_forall_le' hf.continuousOn hp
  refine ⟨c,hc,?_⟩
  intro H hH v
  by_cases hv : v = 0
  · simp [hv,evaluate]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hh := hb (H,u) ⟨hH,by simpa only [mem_sphere,dist_zero_right] using hu⟩
  calc
    c*‖v‖^2 ≤ evaluate H u u*‖v‖^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _ = evaluate H v v := by
      rw [evaluate_smul_both]
      field_simp

end ClosedSurfaceR4.PhaseMean

end

end OAI
