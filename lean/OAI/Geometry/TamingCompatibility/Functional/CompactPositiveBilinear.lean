import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set

lemma compact_positive_bilinear_bounds {Y E : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {K : Set Y} (hK : IsCompact K) {g : Y → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContinuousOn g K) (hpos : ∀ z ∈ K, ∀ v : E, v ≠ 0 → 0 < g z v v) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : E,
      m*‖v‖^2 ≤ g z v v ∧ g z v v ≤ M*‖v‖^2 := by
  by_cases hne : K.Nonempty
  · let q : Y × E → ℝ := fun x => g x.1 x.2 x.2
    have hq : ContinuousOn q (K ×ˢ Metric.sphere (0:E) 1) :=
      ((hg.comp continuousOn_fst (fun _ hx => hx.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨x,hx,hmin⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMinOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    have hxnorm : ‖x.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
    have hqx : 0 < q x := hpos x.1 hx.1 x.2 (by intro h; simp [h] at hxnorm)
    obtain ⟨y,hy,hmax⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMaxOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    refine ⟨q x,max (q y) 1,hqx,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let w := ‖v‖⁻¹ • v
      have hw : w ∈ Metric.sphere (0:E) 1 := by
        simp [w,norm_smul,inv_mul_cancel₀ hnv]
      have hid : g z w w * ‖v‖^2 = g z v v := by
        simp only [w,map_smul,_root_.smul_apply,smul_eq_mul]
        field_simp
      have hlo := mul_le_mul_of_nonneg_right (hmin (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)) (sq_nonneg ‖v‖)
      have hup := mul_le_mul_of_nonneg_right
        ((hmax (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)).trans (le_max_left (q y) 1)) (sq_nonneg ‖v‖)
      change q x * ‖v‖^2 ≤ g z w w * ‖v‖^2 at hlo
      change g z w w * ‖v‖^2 ≤ max (q y) 1 * ‖v‖^2 at hup
      rw [hid] at hlo hup
      exact ⟨hlo,hup⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro z hz
    exact (hne ⟨z,hz⟩).elim
end TamingCompatibility

end

end OAI
