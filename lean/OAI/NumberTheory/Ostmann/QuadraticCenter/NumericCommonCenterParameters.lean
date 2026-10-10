import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterMargins
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_nat_condition_of_logBand {P : ℕ → Prop} (hP : ∀ᶠ Z : ℕ in atTop, P Z) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2 ≤ Real.log Z → P Z := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hP
  filter_upwards [eventually_ge_atTop (2*Real.log (N+1:ℕ)+2),
    eventually_ge_atTop (1:ℝ)] with T hT hTpos
  intro Z hZ
  have hlogZ : 0 < Real.log Z := by linarith
  have hZpos : (0:ℝ)<Z := by
    have := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ
    linarith
  have hNZ : ((N+1:ℕ):ℝ)≤Z := by
    apply (Real.log_le_log_iff (by positivity) hZpos).mp
    linarith
  exact hN Z (by exact_mod_cast (show (N:ℝ)≤Z by push_cast at hNZ; linarith))

theorem eventually_parameter_le_modulus_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2 ≤ Real.log Z → T ≤ (Z:ℝ)^ε := by
  have hh := Real.isLittleO_log_id_atTop.bound (half_pos hε)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with T hh hT
  intro Z hZ
  have hTpos : 0<T := by linarith
  have hlogT : 0≤Real.log T := Real.log_nonneg hT
  have hlogZ : 0<Real.log Z := by linarith
  have hZpos : (0:ℝ)<Z := by
    have := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ
    linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg hlogT,abs_of_nonneg hTpos.le,id_eq] at hh
  rw [Real.rpow_def_of_pos hZpos]
  calc
    T = Real.exp (Real.log T) := (Real.exp_log hTpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hZ hε.le])

theorem eventually_commonCenter_moment_le_T :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2 ≤ Real.log Z →
      (evenMomentParameter (parameterX T) Z:ℝ)≤T := by
  filter_upwards [eventually_evenMomentParameter_bound,
    eventually_mul_rpow_le_rpow 14 (by norm_num : (3/5:ℝ)<1)] with T hk hp
  intro Z hZ
  exact (hk Z hZ).trans (by simpa only [Real.rpow_one] using hp)

theorem eventually_prime_count_power_lower (c : ℝ) (hc : 0 < c) :
    ∀ᶠ Z : ℕ in atTop, ∀ J : ℕ, c*(Z:ℝ)/Real.log Z ≤ (J:ℝ) →
      (Z:ℝ)^(9/10:ℝ)≤J := by
  have hn : Tendsto (fun Z:ℕ => (Z:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh := hn.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/10)).bound hc)
  filter_upwards [hh,eventually_ge_atTop (2:ℕ)] with Z hh hZ
  intro J hJ
  have hZpos : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hZ1 : (1:ℝ)≤Z := by exact_mod_cast (show 1≤Z by omega)
  have hlog : 0<Real.log Z := Real.log_pos (by exact_mod_cast (show 1<Z by omega))
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog.le,
    abs_of_nonneg (Real.rpow_nonneg hZpos.le _)] at hh
  have hid : (Z:ℝ)^(1/10:ℝ)*(Z:ℝ)^(9/10:ℝ)=(Z:ℝ) := by
    rw [←Real.rpow_add hZpos]
    norm_num
  apply le_trans _ hJ
  apply (le_div_iff₀ hlog).mpr
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hZpos.le (9/10:ℝ))
  nlinarith [hid]

theorem moment_order_X_power_bound {X Z : ℕ} (hX : 1≤X) (hZ : 2≤Z) :
    10≤evenMomentParameter X Z ∧
      (X:ℝ)≤(Z:ℝ)^(evenMomentParameter X Z-10) := by
  have hXpos : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hXlog : 0≤Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hZpos : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hZlog : 0<Real.log Z := Real.log_pos (by exact_mod_cast (show 1<Z by omega))
  have hratio : 0≤Real.log X/Real.log Z := by positivity
  have hb := (evenMomentParameter_bounds X Z (by positivity)).1
  have hk : 10≤evenMomentParameter X Z := by exact_mod_cast (by linarith : (10:ℝ)≤evenMomentParameter X Z)
  refine ⟨hk,?_⟩
  have hmul := mul_le_mul_of_nonneg_right hb hZlog.le
  rw [add_mul,div_mul_cancel₀ _ hZlog.ne'] at hmul
  have he : Real.log X≤((evenMomentParameter X Z-10:ℕ):ℝ)*Real.log Z := by
    rw [Nat.cast_sub hk]
    push_cast
    nlinarith
  have hexp := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log hXpos,Real.exp_nat_mul,Real.exp_log hZpos] using hexp

theorem eventually_commonCenterElementaryBounds (c : ℝ) (hc : 0<c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2≤Real.log Z →
      ∀ J : ℕ, c*(Z:ℝ)/Real.log Z≤(J:ℝ) → J≤2*Z →
        CommonCenterElementaryBounds (parameterX T) Z J (evenMomentParameter (parameterX T) Z) := by
  have hlarge : ∀ᶠ Z:ℕ in atTop, (100:ℝ)≤(Z:ℝ)^(1/1000:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/1000)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 100
  filter_upwards [eventually_commonCenter_moment_le_T,
    eventually_parameter_le_modulus_rpow (1/10) (by norm_num),
    eventually_nat_condition_of_logBand (eventually_prime_count_power_lower c hc),
    eventually_nat_condition_of_logBand hlarge,
    eventually_nat_condition_of_logBand (eventually_ge_atTop (2:ℕ)),
    parameterX_tendsto.eventually_ge_atTop 1] with T hk hpow hJlower hlarge hZtwo hX
  intro Z hZ J hJ hJupper
  have hZ2 := hZtwo Z hZ
  have horder := moment_order_X_power_bound hX hZ2
  exact ⟨hX,hZ2,horder.1,(hk Z hZ).trans (hpow Z hZ),
    hJlower Z hZ J hJ,hJupper,horder.2,hlarge Z hZ⟩

end Ostmann.QuadraticCenter

end

end OAI
