import Mathlib

namespace OAI

/-! Compact Homogeneous Bounds. -/

section

 

noncomputable section
open Set Metric
namespace KaehlerCalculus
variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

lemma compact_homogeneous_bound {K : Set X} (hK : IsCompact K)
    (p : ℕ) (hp : 0 < p) (F : X → E → ℝ)
    (hF : ContinuousOn (fun q : X × E => F q.1 q.2) (K ×ˢ closedBall 0 1))
    (hhom : ∀ x ∈ K, ∀ r : ℝ, ∀ v, F x (r • v) = r^p*F x v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v, |F x v| ≤ C*‖v‖^p := by
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0:E) 1)).exists_bound_of_continuousOn hF
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    have hh := hhom x hx 0 (0:E)
    simp only [zero_smul,zero_pow (Nat.ne_of_gt hp),zero_mul] at hh
    simp [hh,zero_pow (Nat.ne_of_gt hp)]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hb := hC (x,(‖v‖⁻¹ : ℝ) • v) ⟨hx,by simpa [mem_closedBall,dist_zero_right] using hw.le⟩
  change ‖F x ((‖v‖⁻¹:ℝ) • v)‖ ≤ C at hb
  rw [hhom x hx,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hn)) _)] at hb
  have hh := mul_le_mul_of_nonneg_left (hb.trans (le_max_left C 0)) (pow_nonneg (norm_nonneg v) p)
  have he : ‖v‖^p*((‖v‖⁻¹)^p*|F x v|) = |F x v| := by
    rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hn.ne',one_pow,one_mul]
  rw [he] at hh
  simpa only [mul_comm] using hh

lemma compact_homogeneous_positive {K : Set X} (hK : IsCompact K)
    (F : X → E → ℝ)
    (hF : ContinuousOn (fun q : X × E => F q.1 q.2) (K ×ˢ sphere 0 1))
    (hpos : ∀ x ∈ K, ∀ v ≠ 0, 0 < F x v)
    (hhom : ∀ x ∈ K, ∀ r : ℝ, ∀ v, F x (r • v) = r^2*F x v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ v, δ*‖v‖^2 ≤ F x v := by
  let L := K ×ˢ sphere (0:E) 1
  have hLc : IsCompact L := hK.prod (isCompact_sphere _ _)
  have hp : ∀ q ∈ L, 0 < F q.1 q.2 := by
    rintro ⟨x,v⟩ ⟨hx,hv⟩
    apply hpos x hx v
    intro hv0
    simp [hv0] at hv
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ L, δ ≤ F q.1 q.2 := by
    by_cases hn : L.Nonempty
    · obtain ⟨q,hq,hmin⟩ := hLc.exists_isMinOn hn hF
      exact ⟨_,hp q hq,fun y hy => hmin hy⟩
    · exact ⟨1,by norm_num,fun q hq => (hn ⟨q,hq⟩).elim⟩
  obtain ⟨δ,hδ,hb⟩ := hδ
  refine ⟨δ,hδ,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    have hh := hhom x hx 0 (0:E)
    simp only [zero_smul,zero_pow (by decide : 2 ≠ 0),zero_mul] at hh
    simp [hh]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have h := hb (x,(‖v‖⁻¹:ℝ) • v) ⟨hx,by simpa [mem_sphere,dist_zero_right] using hw⟩
  rw [hhom x hx] at h
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ‖v‖)
  have he : ‖v‖^2*((‖v‖⁻¹)^2*F x v) = F x v := by
    rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hn.ne',one_pow,one_mul]
  rw [he] at hh
  simpa only [mul_comm] using hh
end KaehlerCalculus

end
end

end OAI
