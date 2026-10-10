import OAI.Probability.SLE.Loewner.ForwardInfinityBounds

namespace OAI

/-! The capacity coefficient is obtained directly from the forward ODE,
with an error tending to zero as the initial point tends to infinity. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

theorem forward_far_capacity_error {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (q : ℝ → ℂ) (u : ℝ → ℝ) (z : ℂ)
    (hc : ContinuousOn q (Icc 0 T)) (hq0 : q 0=z)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt q
      (2/(q t-(u t : ℂ))) (Ici t) t)
    (hu : ∀ t ∈ Icc 0 T, |u t| ≤ M)
    (hlarge : 8*(M+T+1) ≤ ‖z‖) :
    ‖z*(q T-z)-2*(T : ℂ)‖ ≤ 4*T*(M+T)/‖z‖ := by
  obtain ⟨hdisp,hcenter⟩ := forward_far_displacement hT hM q u z hc hq0 hd hu hlarge
  have hr : 0 < ‖z‖ := by nlinarith
  have hfac : 4/‖z‖ ≤ 1 := (div_le_one hr).mpr (by nlinarith)
  let e (t : ℝ) : ℂ := z*(q t-z)-2*(t : ℂ)
  have hec : ContinuousOn e (Icc 0 T) := by
    exact (continuousOn_const.mul (hc.sub continuousOn_const)).sub
      (continuous_const.mul Complex.continuous_ofReal).continuousOn
  have hed (t : ℝ) (ht : t ∈ Ico 0 T) : HasDerivWithinAt e
      (z*(2/(q t-(u t : ℂ)))-2) (Ici t) t := by
    have hl : HasDerivWithinAt (fun s : ℝ => (2:ℂ)*(s:ℂ)) 2 (Ici t) t := by
      convert! ((hasDerivAt_id t).ofReal_comp.const_mul (2:ℂ)).hasDerivWithinAt using 1
      simp
    exact (((hd t ht).sub_const z).const_mul z).sub hl
  have heb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖z*(2/(q t-(u t : ℂ)))-2‖ ≤ 4*(M+T)/‖z‖ := by
    have ht' := Ico_subset_Icc_self ht
    have hden := hcenter t ht'
    have hdenpos : 0 < ‖q t-(u t : ℂ)‖ := (half_pos hr).trans_le hden
    have hne : q t-(u t : ℂ) ≠ 0 := norm_pos_iff.mp hdenpos
    have hdispt : ‖q t-z‖ ≤ T := by
      have hm := mul_le_mul_of_nonneg_right hfac ht.1
      exact (hdisp t ht').trans (hm.trans (by simpa using ht'.2))
    have hnum : ‖z-q t+(u t : ℂ)‖ ≤ M+T := by
      have hh := norm_add_le (z-q t) (u t : ℂ)
      rw [norm_sub_rev z (q t),Complex.norm_real,Real.norm_eq_abs] at hh
      linarith [hu t ht']
    have heq : z*(2/(q t-(u t : ℂ)))-2 =
        2*(z-q t+(u t : ℂ))/(q t-(u t : ℂ)) := by
      field_simp [hne]
      ring
    rw [heq,norm_div,norm_mul]
    norm_num only [norm_ofNat]
    calc
      2*‖z-q t+(u t : ℂ)‖/‖q t-(u t : ℂ)‖
          ≤ 2*(M+T)/‖q t-(u t : ℂ)‖ := by gcongr
      _ ≤ 2*(M+T)/(‖z‖/2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hr) hden
      _ = 4*(M+T)/‖z‖ := by ring
  have hh := norm_image_sub_le_of_norm_deriv_right_le_segment hec hed heb T ⟨hT,le_rfl⟩
  have he0 : e 0=0 := by simp [e,hq0]
  rw [he0,sub_zero,sub_zero] at hh
  exact hh.trans_eq (by ring)

end SLEExactGauge

end

end OAI
