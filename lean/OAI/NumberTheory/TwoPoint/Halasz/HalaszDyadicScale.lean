import OAI.NumberTheory.TwoPoint.Halasz.HalaszFirstOriginalMean

namespace OAI

/-! The dyadic blocks above the square-root cutoff stay inside the
original pretentious scale, with uniform logarithmic errors. -/

namespace TwoPointCorrelations

lemma halasz_dyadic_original_scale {X N : ℕ} (hX : 2 ≤ X)
    (hN : Real.sqrt (X:ℝ) ≤ N) :
    X ≤ N^3 ∧ Real.log (X:ℝ)/2 ≤ Real.log N := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hN0 : 0 < (N:ℝ) := (Real.sqrt_pos.2 hX0).trans_le hN
  have hn : 1 ≤ N := by exact_mod_cast (show 0<N by exact_mod_cast hN0)
  have hsq : (X:ℝ) ≤ (N:ℝ)^2 := by
    nlinarith [Real.sq_sqrt hX0.le,Real.sqrt_nonneg (X:ℝ)]
  have hsqN : X ≤ N^2 := by exact_mod_cast hsq
  refine ⟨hsqN.trans (pow_le_pow_right₀ hn (by norm_num : 2≤3)),?_⟩
  have hl := Real.log_le_log hX0 hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

lemma halasz_dyadic_error_comparison {L l : ℝ} (hL : 0 < L) (hlo : L/2 ≤ l) :
    l^(-1/700:ℝ) ≤ 2*L^(-1/700:ℝ) := by
  have htwo : (2:ℝ)^(1/700:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤2 by norm_num) (show (1/700:ℝ)≤1 by norm_num)
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0<L/2) hlo
    (show (-1/700:ℝ)≤0 by norm_num)
  have he : (2:ℝ)^(-1/700:ℝ)=((2:ℝ)^(1/700:ℝ))⁻¹ := by
    rw [show (-1/700:ℝ)=-(1/700:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ)≤2),he,div_inv_eq_mul] at hh
  exact hh.trans (by nlinarith only
    [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hL.le (-1/700))])

lemma halasz_dyadic_short_height {L l : ℝ} (hL : 0 ≤ L) (hlo : L/2 ≤ l) :
    Real.sqrt L/2 ≤ Real.sqrt l := by
  have hl : 0 ≤ l := by linarith
  nlinarith [Real.sq_sqrt hL,Real.sq_sqrt hl,Real.sqrt_nonneg L,Real.sqrt_nonneg l]

lemma halasz_log_le_two_sqrt {X : ℝ} (hX : 0 < X) : Real.log X ≤ 2*Real.sqrt X := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hh := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hX.le] at hh
  linarith

lemma halasz_sqrt_cutoff_error {X : ℝ} (hX : 1 ≤ X) (hL : 1 ≤ Real.log X) :
    (⌈Real.sqrt X⌉₊:ℝ)/X ≤ 4*(Real.log X)^(-1/700:ℝ) ∧
    1 ≤ 2*(Real.log X)^(-1/700:ℝ)*(⌈Real.sqrt X⌉₊:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hlog0 : 0 < Real.log X := by linarith
  have hs : 1 ≤ Real.sqrt X := (Real.one_le_sqrt).2 hX
  have hs0 : 0 < Real.sqrt X := by linarith
  have hwlo : Real.sqrt X ≤ (⌈Real.sqrt X⌉₊:ℝ) := Nat.le_ceil _
  have hwhi : (⌈Real.sqrt X⌉₊:ℝ) ≤ 2*Real.sqrt X := by
    have hh := Nat.ceil_lt_add_one (Real.sqrt_nonneg X)
    linarith
  have hlog := halasz_log_le_two_sqrt hX0
  have hp : 1/Real.log X ≤ (Real.log X)^(-1/700:ℝ) := by
    simpa only [Real.rpow_neg_one,one_div] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-1:ℝ)≤-1/700)
  constructor
  · have hh : (⌈Real.sqrt X⌉₊:ℝ)/X ≤ 4/Real.log X := by
      apply (div_le_div_iff₀ hX0 hlog0).mpr
      have hm := mul_le_mul_of_nonneg_right hlog (by positivity : 0≤2*Real.sqrt X)
      nlinarith [Real.sq_sqrt hX0.le,mul_le_mul_of_nonneg_right hwhi hlog0.le]
    apply hh.trans
    calc
      4/Real.log X = 4*(1/Real.log X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  · have hh : Real.log X ≤ 2*(⌈Real.sqrt X⌉₊:ℝ) := by linarith
    have hd : 1 ≤ 2*(⌈Real.sqrt X⌉₊:ℝ)/Real.log X :=
      (le_div_iff₀ hlog0).mpr (by simpa only [one_mul] using hh)
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*(⌈Real.sqrt X⌉₊:ℝ))
    apply hd.trans
    convert hm using 1 <;> ring

end TwoPointCorrelations

end OAI
