import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.CompactQuadratic
open Set
variable {Y V : Type*} [TopologicalSpace Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem lower_bound {K : Set Y} (hK : IsCompact K)
    (Q : Y → V →L[ℝ] V →L[ℝ] ℝ) (hQ : ContinuousOn Q K)
    (hpos : ∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < Q x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : V, ‖v‖^2 ≤ C * Q x v v := by
  have hc : IsCompact (K ×ˢ Metric.sphere (0 : V) 1) :=
    hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun xv : Y × V => Q xv.1 xv.2 xv.2)
      (K ×ˢ Metric.sphere (0 : V) 1) :=
    ((hQ.comp continuous_fst.continuousOn (fun _ h => h.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  by_cases he : (K ×ˢ Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn he hcont
    have hzNorm : ‖z.2‖ = 1 := by simpa using hz.2
    have hm : 0 < Q z.1 z.2 z.2 := hpos z.1 hz.1 z.2 (by
      intro h; simp only [h,norm_zero] at hzNorm; linarith)
    refine ⟨(Q z.1 z.2 z.2)⁻¹,inv_pos.mpr hm,?_⟩
    intro x hx v
    by_cases hv : v=0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have heval : Q x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = Q x v v / ‖v‖^2 := by
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    have hmin' := hmin (show (x,‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : V) 1 from ⟨hx,hu⟩)
    change Q z.1 z.2 z.2 ≤ Q x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at hmin'
    rw [heval] at hmin'
    have hl := (le_div_iff₀ (sq_pos_of_pos hn)).mp hmin'
    calc ‖v‖^2 ≤ Q x v v / Q z.1 z.2 z.2 := (le_div_iff₀ hm).mpr (by nlinarith)
         _ = (Q z.1 z.2 z.2)⁻¹ * Q x v v := by ring
  · refine ⟨1,by norm_num,?_⟩
    intro x hx v
    have hv : v=0 := by
      by_contra hv
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      apply he
      refine ⟨(x,‖v‖⁻¹ • v),hx,?_⟩
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    simp [hv]
end TamingCompatibility.CompactQuadratic

end

end OAI
