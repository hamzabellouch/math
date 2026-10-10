import Mathlib
import OAI.Combinatorics.KMedian.Analysis.BernsteinFalse
import OAI.Combinatorics.KMedian.Analysis.BernsteinTrue
import OAI.Combinatorics.KMedian.Analysis.ChargeTransfer

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem quadratic_of_end_slopes {a b c r : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hbc : 0 ≤ b+c) (hr0 : 0 ≤ r) (_hr : r ≤ 1) :
    0 ≤ a+b*r+c*r^2 := by
  have h1 := mul_nonneg hbc (sq_nonneg r)
  have h2 := mul_nonneg (mul_nonneg hb hr0) (sub_nonneg.mpr _hr)
  nlinarith only [ha, h1, h2]

private theorem quadratic_of_discriminant {a b c r : ℝ} (ha : 0 ≤ a)
    (hd : 0 < 4*a*c-b^2) : 0 ≤ a+b*r+c*r^2 := by
  have hc : 0 < c := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hn)
    nlinarith only [hp, hd, sq_nonneg b]
  have hs := sq_nonneg (2*c*r+b)
  have hid : (2*c*r+b)^2+(4*a*c-b^2) = 4*c*(a+b*r+c*r^2) := by ring
  have hprod : 0 < c*(a+b*r+c*r^2) := by nlinarith only [hs, hd, hid]
  exact (pos_of_mul_pos_right hprod hc.le).le

private theorem quadratic_of_total {a b c r : ℝ} (ha : 0 ≤ a)
    (ht : 0 ≤ a+b+c) (hd : 0 ≤ a-c) (hr0 : 0 ≤ r) (_hr : r ≤ 1) :
    0 ≤ a+b*r+c*r^2 := by
  have h1 := mul_nonneg hr0 ht
  have h2 := add_nonneg (mul_nonneg (sub_nonneg.mpr _hr) ha) (mul_nonneg hr0 hd)
  have h3 := mul_nonneg (sub_nonneg.mpr _hr) h2
  nlinarith only [h1, h3]

noncomputable def bernCoeff (s : Bool) (i : ℕ) (X r : ℝ) : ℝ :=
  B0 s i X + B1 s i X*r+B2 s i X*r^2

theorem bernCoeff_0_0_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 0 X r := by
  have ha := B0_0_0_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_0_0_positive hX0 hX
  have hbc := sum12_0_0_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

theorem bernCoeff_0_1_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 1 X r := by
  have ha := B0_0_1_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_0_1_positive hX0 hX
  have hbc := sum12_0_1_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

theorem bernCoeff_0_2_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 2 X r := by
  have ha := B0_0_2_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/20
  · have hb := B1_0_2_positive hX0 hcut
    have hc := B2_0_2_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_0_2_positive (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

theorem bernCoeff_0_3_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 3 X r := by
  have ha := B0_0_3_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 3/200
  · have hb := B1_0_3_positive hX0 hcut
    have hc := B2_0_3_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_0_3_positive (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

theorem bernCoeff_1_0_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 0 X r := by
  have ha := B0_1_0_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_1_0_positive hX0 hX
  have hbc := sum12_1_0_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

theorem bernCoeff_1_1_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 1 X r := by
  have ha := B0_1_1_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_1_1_positive hX0 hX
  have hbc := sum12_1_1_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

theorem bernCoeff_1_2_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 2 X r := by
  have ha := B0_1_2_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/5
  · have hb := B1_1_2_positive hX0 hcut
    have hc := B2_1_2_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_1_2_positive (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

theorem bernCoeff_1_3_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 3 X r := by
  have ha := B0_1_3_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/10
  · have hb := B1_1_3_positive hX0 hcut
    have hc := B2_1_3_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · by_cases hmid : X ≤ 3/4
    · have hd := discr_1_3_positive (le_of_not_ge hcut) hmid
      exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)
    · have ht := total_1_3_positive (le_of_not_ge hmid) hX
      have hd := diff02_1_3_positive (le_of_not_ge hmid) hX
      exact quadratic_of_total ha (by dsimp only [total] at ht; linarith) (by linarith) hr0 _hr

theorem charge_expansion (s : Bool) (X η r : ℝ) :
    ChargeTransfer.charge (p X) (v X) (k X) (H s X) (1-X) (X*η) r s -
      (1/5000)*(r+(X*η)^2) =
    bernCoeff s 0 X r*(1-η)^3+3*bernCoeff s 1 X r*η*(1-η)^2+
      3*bernCoeff s 2 X r*η^2*(1-η)+bernCoeff s 3 X r*η^3 := by
  dsimp only [ChargeTransfer.charge, ChargeTransfer.F1, ChargeTransfer.F2,
    ChargeTransfer.F3, ChargeTransfer.F4, ChargeTransfer.c, bernCoeff,
    B0, B1, B2, N, l, c]
  have hb : ChargeTransfer.bit s = bit s := rfl
  rw [hb]
  norm_num
  ring

theorem polynomial_charge_margin {X w r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ X) (hr0 : 0 ≤ r) (_hr : r ≤ 1) (s : Bool) :
    (1/5000)*(r+w^2) ≤ ChargeTransfer.charge (p X) (v X) (k X) (H s X) (1-X) w r s := by
  have hcoeff : ∀ i : Fin 4, 0 ≤ bernCoeff s i X r := by
    intro i
    fin_cases i <;> cases s
    · exact bernCoeff_0_0_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_1_0_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_0_1_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_1_1_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_0_2_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_1_2_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_0_3_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_1_3_nonneg hX0 hX hr0 _hr
  have hη : ∃ η : ℝ, 0 ≤ η ∧ η ≤ 1 ∧ w = X*η := by
    by_cases hzero : X = 0
    · exact ⟨0, le_refl _, zero_le_one, by rw [hzero]; linarith⟩
    · have hpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hzero)
      refine ⟨w/X, div_nonneg hw0 hX0, (div_le_one hpos).mpr hw, ?_⟩
      field_simp
  obtain ⟨η, hη0, hη1, hwη⟩ := hη
  have hηc : 0 ≤ 1-η := sub_nonneg.mpr hη1
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  have h2 := hcoeff 2
  have h3 := hcoeff 3
  have hbern : 0 ≤ bernCoeff s 0 X r*(1-η)^3+3*bernCoeff s 1 X r*η*(1-η)^2+
      3*bernCoeff s 2 X r*η^2*(1-η)+bernCoeff s 3 X r*η^3 := by
    positivity
  rw [←charge_expansion] at hbern
  rw [hwη]
  linarith only [hbern]

end MetricKMedian.Certificates


end
end

end OAI
