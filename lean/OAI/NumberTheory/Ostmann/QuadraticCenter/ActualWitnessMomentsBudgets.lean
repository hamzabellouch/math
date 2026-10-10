import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsScalar

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem witness_mesh_error_le_half {Z : ℕ} (hZ : 2 ≤ Z) :
    (Z:ℝ)^(-(66:ℝ)) ≤ 1/2 := by
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast (show 1 ≤ Z by omega)
  calc
    _ ≤ (Z:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZr (by norm_num)
    _ = (1:ℝ)/Z := by rw [Real.rpow_neg_one,one_div]
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hZ)

theorem witness_large_mesh_budget {Z : ℕ} (hZ : 2 ≤ Z) {K : ℝ} (hK : 4000 ≤ K) :
    Real.exp ((13/2000:ℝ)*K)+(Z:ℝ)^(-(66:ℝ)) ≤ Real.exp ((7/1000:ℝ)*K) := by
  have herror := witness_mesh_error_le_half hZ
  have hone : 1 ≤ Real.exp ((13/2000:ℝ)*K) := Real.one_le_exp (by linarith)
  have htwo : (2:ℝ) ≤ Real.exp (K/2000) := by linarith [Real.add_one_le_exp (K/2000)]
  have hh := mul_le_mul_of_nonneg_right htwo (Real.exp_pos ((13/2000:ℝ)*K)).le
  rw [←Real.exp_add] at hh
  have hid : K/2000+(13/2000:ℝ)*K=(7/1000:ℝ)*K := by ring
  rw [hid] at hh
  linarith

theorem witness_offevent_mesh_budget {Z : ℕ} (hZ : 2 ≤ Z) {K : ℝ} (hK : 4000 ≤ K) :
    Real.exp (-K/4)+(Z:ℝ)^(-(66:ℝ)) ≤ 1 := by
  have herror := witness_mesh_error_le_half hZ
  have htwo : (2:ℝ) ≤ Real.exp (K/4) := by linarith [Real.add_one_le_exp (K/4)]
  have hh : Real.exp (-K/4) ≤ 1/2 := by
    rw [show -K/4=-(K/4) by ring,Real.exp_neg,inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) htwo
  linarith

theorem witness_nontrivial_mesh_budget {Z k : ℕ} (hZ : 2 ≤ Z)
    (hlog : 4000 ≤ Real.log Z) (hcount : (2:ℝ)^k ≤ (Z:ℝ)^(1/8:ℝ)) :
    (2:ℝ)^k*((Z:ℝ)^(-(1/4:ℝ))+(Z:ℝ)^(-(66:ℝ))) ≤ 1 := by
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast (show 1 ≤ Z by omega)
  have hZpos : (0:ℝ) < Z := by linarith
  have hmesh : (Z:ℝ)^(-(66:ℝ)) ≤ (Z:ℝ)^(-(1/4:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hZr (by norm_num)
  have htwo : (2:ℝ) ≤ (Z:ℝ)^(1/8:ℝ) := by
    rw [Real.rpow_def_of_pos hZpos]
    linarith [Real.add_one_le_exp (Real.log Z*(1/8:ℝ))]
  calc
    _ ≤ (Z:ℝ)^(1/8:ℝ)*((Z:ℝ)^(-(1/4:ℝ))+(Z:ℝ)^(-(66:ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ (Z:ℝ)^(1/8:ℝ)*(2*(Z:ℝ)^(-(1/4:ℝ))) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2/(Z:ℝ)^(1/8:ℝ) := by
      rw [show (Z:ℝ)^(1/8:ℝ)*(2*(Z:ℝ)^(-(1/4:ℝ)))=2*((Z:ℝ)^(1/8:ℝ)*(Z:ℝ)^(-(1/4:ℝ))) by ring,
        ←Real.rpow_add hZpos]
      norm_num
      rw [Real.rpow_neg (Nat.cast_nonneg Z)]
      ring
    _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hZpos _)).mpr htwo

theorem eventually_witness_moment_budgets :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      adaptiveArrayThreshold ≤ Z ∧ 4000 ≤ (auxiliaryK Z z:ℝ) ∧
      (auxiliaryK Z z:ℝ) ≤ Real.log Z ∧
      (2:ℝ)^(evenMomentParameter (parameterX T) Z) ≤ (Z:ℝ)^(1/8:ℝ) := by
  filter_upwards [eventually_auxiliaryK_bounds,eventually_auxiliaryK_le_log 1 (by norm_num),
    eventually_evenMomentParameter_bound,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 4000,
    eventually_ge_atTop (2*(adaptiveArrayThreshold:ℝ)),
    eventually_mul_rpow_le_rpow (224*Real.log 2) (a:=3/5) (b:=1) (by norm_num)]
    with T hK hKlog hk hT hTh hg
  intro Z z hZl hZu hz hzl hzu
  have hZbig : adaptiveArrayThreshold ≤ Z := by
    have hh := Real.log_le_self (Nat.cast_nonneg Z : (0:ℝ) ≤ _)
    have hh' : (adaptiveArrayThreshold:ℝ) ≤ Z := by linarith
    exact_mod_cast hh'
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hZpos : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  refine ⟨hZbig,hT.trans (hK Z z hZl hZu hz hzl hzu).1,
    by simpa only [one_mul] using hKlog Z z hZl hZu hz hzl hzu,?_⟩
  have hkle := mul_le_mul_of_nonneg_right (hk Z hZl) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hexp : (evenMomentParameter (parameterX T) Z:ℝ)*Real.log 2 ≤ Real.log Z/8 := by
    rw [Real.rpow_one] at hg
    nlinarith
  have he := Real.exp_le_exp.mpr hexp
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 2)] at he
  simpa only [Real.rpow_def_of_pos hZpos,div_eq_mul_inv,one_mul] using he

end Ostmann.QuadraticCenter

end

end OAI
