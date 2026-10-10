import Mathlib

namespace OAI

/-! Uniform bounds for forward Loewner trajectories far from the origin.
Only the bounded driver on the fixed time interval is used. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma forward_far_center_lower {q z : ℂ} {u M A r : ℝ}
    (hr : r=‖z‖) (hu : |u| ≤ M) (hq : ‖q-z‖ ≤ A)
    (hsize : 2*(M+A) ≤ r) : r/2 ≤ ‖q-(u : ℂ)‖ := by
  have h1 := norm_le_norm_sub_add z q
  have h2 := norm_le_norm_sub_add q (u : ℂ)
  rw [norm_sub_rev z q] at h1
  rw [Complex.norm_real,Real.norm_eq_abs] at h2
  linarith

theorem forward_far_displacement {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (q : ℝ → ℂ) (u : ℝ → ℝ) (z : ℂ)
    (hc : ContinuousOn q (Icc 0 T)) (hq0 : q 0=z)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt q
      (2/(q t-(u t : ℂ))) (Ici t) t)
    (hu : ∀ t ∈ Icc 0 T, |u t| ≤ M)
    (hlarge : 8*(M+T+1) ≤ ‖z‖) :
    (∀ t ∈ Icc 0 T, ‖q t-z‖ ≤ (4/‖z‖)*t) ∧
      ∀ t ∈ Icc 0 T, ‖z‖/2 ≤ ‖q t-(u t : ℂ)‖ := by
  let r : ℝ := ‖z‖
  have hr : 0 < r := by dsimp [r]; nlinarith
  have hr8 : 8 ≤ r := by dsimp [r]; nlinarith
  have hfac : 8/r ≤ 1 := (div_le_one hr).mpr hr8
  have hbnd (t : ℝ) (ht : t ∈ Icc 0 T) : 1+(8/r)*t ≤ 1+T := by
    have hh := mul_le_mul_of_nonneg_right hfac ht.1
    nlinarith [ht.2]
  have hsize : 2*(M+(1+T)) ≤ r := by dsimp [r]; nlinarith
  have hrough : ∀ t ∈ Icc 0 T, ‖q t-z‖ ≤ 1+(8/r)*t := by
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (hc.sub continuousOn_const) (fun t ht => (hd t ht).sub_const z)
      (B := fun t => 1+(8/r)*t) (B' := fun _ => 8/r)
    · simp [hq0]
    · intro t
      convert! ((hasDerivAt_id t).const_mul (8/r)).const_add 1 using 1
      simp
    · intro t ht he
      have hcenter := forward_far_center_lower (q := q t) (z := z)
        (u := u t) (M := M) (A := 1+T) rfl (hu t (Ico_subset_Icc_self ht))
        (he.le.trans (hbnd t (Ico_subset_Icc_self ht))) hsize
      have hnorm : ‖2/(q t-(u t : ℂ))‖ ≤ 4/r := by
        rw [norm_div]
        norm_num only [norm_ofNat]
        have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
          (half_pos hr) hcenter
        convert! hh using 1
        field_simp
        ring
      exact hnorm.trans_lt (div_lt_div_of_pos_right (by norm_num) hr)
  have hcenter (t : ℝ) (ht : t ∈ Icc 0 T) : r/2 ≤ ‖q t-(u t : ℂ)‖ :=
    forward_far_center_lower rfl (hu t ht) ((hrough t ht).trans (hbnd t ht)) hsize
  refine ⟨?_,hcenter⟩
  have hderiv (t : ℝ) (ht : t ∈ Ico 0 T) : ‖2/(q t-(u t : ℂ))‖ ≤ 4/r := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
      (half_pos hr) (hcenter t (Ico_subset_Icc_self ht))
    convert! hh using 1
    field_simp
    ring
  intro t ht
  simpa only [hq0,sub_zero] using
    norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hderiv t ht

end SLEExactGauge

end

end OAI
