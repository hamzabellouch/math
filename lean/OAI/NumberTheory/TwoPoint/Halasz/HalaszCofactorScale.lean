import OAI.NumberTheory.TwoPoint.Halasz.HalaszOffCenterCofactor
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCost

namespace OAI

/-! The cutoffs of extra-prime cofactors stay at the original logarithmic
scale. These bounds include the floors used in the actual polynomials. -/
namespace TwoPointCorrelations

open Filter

theorem halasz_cofactor_floor_scale (X₀ : ℝ) (n₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, 1 ≤ a →
      a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      let m := ⌊(N:ℝ)/a⌋₊
      let n := ⌊(2*N:ℝ)/a⌋₊
      X₀ ≤ (m:ℝ) ∧ n₀ ≤ n ∧ n ≤ 2*N ∧ 2*N ≤ n^3 ∧
      Real.log N/2 ≤ Real.log (n:ℝ) ∧ Real.log (n:ℝ) ≤ 2*Real.log N ∧
      Real.log (n:ℝ)^8 ≤ N := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (isLittleO_pow_exp_pos_mul_atTop 8 (b := 1) (by norm_num)).bound
    (show (0:ℝ)<1/256 by norm_num)
  filter_upwards [hlog.eventually hb,
    hlog.eventually (eventually_ge_atTop (10+2*|X₀|+2*(n₀:ℝ))),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1000:ℝ)),
    eventually_ge_atTop 2] with N hb hL hLL hN
  intro a ha haU
  let L := Real.log (N:ℝ)
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hL0 : 0 < L := by dsimp [L]; nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have ha0 : 0 < a := by linarith
  have hlen := halasz_extra_cofactor_length hL0.le hLL ha0 haU
    (show Real.exp L ≤ N by rw [Real.exp_log hN0])
  have hbig : X₀+1 ≤ Real.exp ((999/1000:ℝ)*L) ∧
      (n₀:ℝ) ≤ Real.exp ((999/1000:ℝ)*L) ∧ 2 ≤ Real.exp ((999/1000:ℝ)*L) := by
    have he := Real.add_one_le_exp ((999/1000:ℝ)*L)
    have hx := le_abs_self X₀
    dsimp [L] at he
    constructor
    · nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
    · constructor <;> nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hx : 2 ≤ (N:ℝ)/a := hbig.2.2.trans hlen
  have hmX : X₀ ≤ (m:ℝ) := by
    have hf := Nat.lt_floor_add_one ((N:ℝ)/a)
    change (N:ℝ)/a < (m:ℝ)+1 at hf
    linarith [hbig.1.trans hlen]
  have hnlow : (N:ℝ)/a ≤ (n:ℝ) := by
    have hf := Nat.lt_floor_add_one ((2*N:ℝ)/a)
    change (2*N:ℝ)/a < (n:ℝ)+1 at hf
    have he : (2*N:ℝ)/a=2*((N:ℝ)/a) := by ring
    rw [he] at hf
    linarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hnscale := hlen.trans hnlow
  have hnlarge : n₀ ≤ n := by exact_mod_cast hbig.2.1.trans hnscale
  have hnupper : n ≤ 2*N := by
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      div_le_self (show (0:ℝ) ≤ 2*N by positivity) ha
  have hn0 : 0 < (n:ℝ) := (Real.exp_pos _).trans_le hnscale
  have hloglow : (999/1000:ℝ)*L ≤ Real.log (n:ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hnscale
  have hlogupper : Real.log (n:ℝ) ≤ 2*L := by
    have hh := Real.log_le_log hn0
      (show (n:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast hnupper)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    have htwo := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    dsimp [L]
    linarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hncube : 2*N ≤ n^3 := by
    have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hpow := pow_le_pow_left₀ (Real.exp_pos ((999/1000:ℝ)*L)).le hnscale 3
    have hNexp : (N:ℝ)^2=Real.exp (2*L) := by
      rw [show 2*L=L+L by ring,Real.exp_add,Real.exp_log hN0]
      ring
    have hexp : Real.exp (2*L) ≤ (Real.exp ((999/1000:ℝ)*L))^3 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num
      nlinarith
    have hh : 2*(N:ℝ) ≤ (n:ℝ)^3 := by nlinarith
    exact_mod_cast hh
  have hwidth : Real.log (n:ℝ)^8 ≤ N := by
    have hnlog0 : 0 ≤ Real.log (n:ℝ) := by nlinarith
    have hp := pow_le_pow_left₀ hnlog0 hlogupper 8
    change ‖L^8‖ ≤ (1/256:ℝ)*‖Real.exp (1*L)‖ at hb
    rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ L^8),
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos L),Real.exp_log hN0] at hb
    norm_num [mul_pow] at hp
    nlinarith
  exact ⟨hmX,hnlarge,hnupper,hncube,by nlinarith,hlogupper,hwidth⟩

lemma halasz_cofactor_scale_decay {L l : ℝ} (hL : 0 < L)
    (hlow : L/2 ≤ l) (hupp : l ≤ 2*L) :
    l^(1/16:ℝ)/2 ≤ L^(1/16:ℝ) ∧ l^(-1/40:ℝ) ≤ 2*L^(-1/40:ℝ) := by
  have hl : 0 < l := by linarith
  have hp1 : (2:ℝ)^(1/16:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤2 by norm_num) (show (1/16:ℝ)≤1 by norm_num)
  have hp2 : (2:ℝ)^(1/40:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤2 by norm_num) (show (1/40:ℝ)≤1 by norm_num)
  constructor
  · have hh := Real.rpow_le_rpow hl.le hupp (show (0:ℝ)≤1/16 by norm_num)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hL.le] at hh
    nlinarith [mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hL.le (1/16))]
  · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0<L/2) hlow
      (show (-1/40:ℝ)≤0 by norm_num)
    have he : (2:ℝ)^(-1/40:ℝ)=((2:ℝ)^(1/40:ℝ))⁻¹ := by
      rw [show (-1/40:ℝ)=-(1/40:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [Real.div_rpow hL.le (by norm_num : (0:ℝ)≤2),he,div_inv_eq_mul] at hh
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hp2 (Real.rpow_nonneg hL.le (-1/40))])

end TwoPointCorrelations

end OAI
