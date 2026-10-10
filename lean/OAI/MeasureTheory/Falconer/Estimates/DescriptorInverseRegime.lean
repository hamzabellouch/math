import OAI.MeasureTheory.Falconer.Fourier.DescriptorDerivativeScale

namespace OAI

/-! # The actual descriptor derivative scale is in the inverse regime

The high-frequency condition and the retained descriptor length give a
uniform gap between the squared derivative scale and the oscillation.
The fixed shell factor four is absorbed before selecting any cells.
-/

namespace Falconer

private theorem dyadic_nat_rpow (N : ℕ) (t : ℝ) :
    ((2 : ℝ)^N)^t = (2 : ℝ)^((N : ℝ)*t) :=
  (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) N t).symm

private theorem dyadic_square_div (u q : ℝ) :
    ((2 : ℝ)^u)^2/(2 : ℝ)^q = (2 : ℝ)^(2*u-q) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem descriptorDerivativeScale_le_square (N L : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hLN : L ≤ N) :
    descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 := by
  let R := (2 : ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hr : R^σ ≤ R := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR hσ1
  have hneg : R^(-50*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hw : max 1 ((2 : ℝ)^L*R^(-50*σ)) ≤ R := by
    apply max_le hR
    calc
      _ ≤ (2 : ℝ)^L*1 := mul_le_mul_of_nonneg_left hneg (by positivity)
      _ ≤ R := by simpa only [mul_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLN
  change R^σ*max 1 ((2 : ℝ)^L*R^(-50*σ)) ≤ R^2
  exact (mul_le_mul hr hw (by positivity) (by positivity)).trans_eq (by ring)

theorem descriptorDerivativeScale_inverse_ratio (N L : ℕ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq : 20*σ*(N : ℝ) ≤ q)
    (hL : (L : ℝ) ≤ q/2+σ*(N : ℝ)) :
    (descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q ≤ ((2 : ℝ)^N)^(-18*σ) := by
  have hσN : 0 ≤ σ*(N : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
  by_cases hw : (2 : ℝ)^L*((2 : ℝ)^N)^(-50*σ) ≤ 1
  · have he : descriptorDerivativeScale N σ L = (2 : ℝ)^((N : ℝ)*σ) := by
      rw [descriptorDerivativeScale,max_eq_left hw,mul_one,dyadic_nat_rpow]
    rw [he,dyadic_square_div,dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  · have he : descriptorDerivativeScale N σ L =
        (2 : ℝ)^((L : ℝ)-49*σ*(N : ℝ)) := by
      rw [descriptorDerivativeScale,max_eq_right (le_of_not_ge hw),
        dyadic_nat_rpow N σ,dyadic_nat_rpow N (-50*σ),← Real.rpow_natCast (2 : ℝ) L,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [he,dyadic_square_div,dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

theorem descriptorDerivativeScale_inverse_regime (N L : ℕ) {σ q : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hLN : L ≤ N)
    (hq : 20*σ*(N : ℝ) ≤ q) (hL : (L : ℝ) ≤ q/2+σ*(N : ℝ)) :
    1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      (descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q ≤ ((2 : ℝ)^N)^(-18*σ) :=
  ⟨descriptorDerivativeScale_ge_one N hσ.le L,
    descriptorDerivativeScale_le_square N L hσ.le hσ1 hLN,
    descriptorDerivativeScale_inverse_ratio N L hσ.le hq hL⟩

theorem eventual_descriptor_inverse_frequency {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (q Λ : ℝ), L ≤ N →
      20*σ*(N : ℝ) ≤ q → (L : ℝ) ≤ q/2+σ*(N : ℝ) →
      (2 : ℝ)^q/4 ≤ Λ →
      1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      1 ≤ Λ ∧ (descriptorDerivativeScale N σ L)^2/Λ ≤ ((2 : ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ 4
  refine ⟨N₀,?_⟩
  intro N hN L q Λ hLN hq hL hΛ
  obtain ⟨hD,hDupper,hratio⟩ := descriptorDerivativeScale_inverse_regime N L hσ hσ1 hLN hq hL
  have hσN : 0 ≤ σ*(N : ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hRq : ((2 : ℝ)^N)^σ ≤ (2 : ℝ)^q := by
    rw [dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hfour : 4 ≤ (2 : ℝ)^q := (hN₀ N hN).trans hRq
  have hΛ1 : 1 ≤ Λ := (by linarith : (1 : ℝ) ≤ (2 : ℝ)^q/4).trans hΛ
  refine ⟨hD,hDupper,hΛ1,?_⟩
  calc
    _ ≤ (descriptorDerivativeScale N σ L)^2/((2 : ℝ)^q/4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΛ
    _ = 4*((descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q) := by ring
    _ ≤ 4*((2 : ℝ)^N)^(-18*σ) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ ((2 : ℝ)^N)^σ*((2 : ℝ)^N)^(-18*σ) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2 : ℝ)^N)^(-17*σ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

theorem dyadic_shell_frequency_lower {a v r : ℝ} (hr : (2 : ℝ)^v/4 ≤ r) :
    (2 : ℝ)^(v-a)/4 ≤ r*(2 : ℝ)^(-a) := by
  calc
    _ = ((2 : ℝ)^v/4)*(2 : ℝ)^(-a) := by
      rw [div_mul_eq_mul_div,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (by positivity)

theorem inverse_frequency_of_scaled_distance {D r s t : ℝ}
    (hs : 0 < s) (hΛ : 1 ≤ r*s) (ht : 1 ≤ t/s) :
    1 ≤ r*t ∧ D^2/(r*t) ≤ D^2/(r*s) := by
  have hr : 0 < r := (mul_pos_iff_of_pos_right hs).mp (zero_lt_one.trans_le hΛ)
  have hst : s ≤ t := by simpa only [one_mul] using (le_div_iff₀ hs).mp ht
  have hmul : r*s ≤ r*t := mul_le_mul_of_nonneg_left hst hr.le
  exact ⟨hΛ.trans hmul,div_le_div_of_nonneg_left (sq_nonneg _)
    (zero_lt_one.trans_le hΛ) hmul⟩

end Falconer

end OAI
