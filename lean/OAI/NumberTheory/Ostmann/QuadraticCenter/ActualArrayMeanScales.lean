import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterTupleBounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScalesGrowth
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductSampling

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem primeProductSamples_band_bounds {P : Finset ℕ} {Z k q : ℕ}
    (hP : ∀ r ∈ P, Z ≤ r ∧ r ≤ 2*Z) (hq : q ∈ primeProductSamples P k) :
    Z^k ≤ q ∧ q ≤ (2*Z)^k := by
  classical
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hq
  have hcard := (Finset.mem_powersetCard.mp hU).2
  constructor
  · calc
      Z^k = Z^U.card := by rw [hcard]
      _ ≤ ∏ p ∈ U,p.val := Finset.pow_card_le_prod U _ Z (fun p _ => (hP p p.property).1)
  · calc
      primeSubsetProduct U = ∏ p ∈ U,p.val := rfl
      _ ≤ (2*Z)^U.card := Finset.prod_le_pow_card U _ (2*Z) (fun p _ => (hP p p.property).2)
      _ = (2*Z)^k := by rw [hcard]

theorem eventually_primeProduct_radius_bounds :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2 ≤ Real.log Z →
      ∀ P : Finset ℕ, (∀ r ∈ P,Z ≤ r ∧ r ≤ 2*Z) →
      ∀ q ∈ primeProductSamples P (evenMomentParameter (parameterX T) Z),
        (Z:ℝ)^10 ≤ (q:ℝ)/parameterX T ∧ (q:ℝ)/parameterX T ≤ (Z:ℝ)^13 := by
  filter_upwards [eventually_parameterX_log_bounds,eventually_evenMomentParameter_bound,
    parameterX_tendsto.eventually_gt_atTop 0,
    eventually_mul_rpow_le_rpow (28*Real.log 2) (a:=3/5) (b:=1) (by norm_num)]
    with T hX hk hXpos hg
  intro Z hZ P hP q hq
  have hT : 0 < T := by linarith [hX.1]
  have hlogZ : 0 < Real.log Z := by linarith
  have hZr : (0:ℝ) < Z := lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ)
  have hZn : 0 < Z := by exact_mod_cast hZr
  have hkspan := evenMomentParameter_bounds (parameterX T) Z
    (show 0 ≤ Real.log (parameterX T:ℝ)/Real.log Z+10 by
      have : 0 ≤ Real.log (parameterX T:ℝ) := by linarith [hX.2.1]
      positivity)
  have hsmall : (evenMomentParameter (parameterX T) Z:ℝ)*Real.log 2 ≤ Real.log Z := by
    have hm := mul_le_mul_of_nonneg_right (hk Z hZ) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    rw [Real.rpow_one] at hg
    nlinarith
  have hprod := primeProductSamples_band_bounds hP hq
  exact tuple_scale_of_log_bounds (parameterX T) Z q _ hXpos hZn hlogZ
    hkspan.1 hkspan.2.le hsmall hprod.1 hprod.2

theorem primeProduct_array_cutoff {Z L : ℕ} (hZ : 1 ≤ Z) {R : ℝ}
    (hR : R ≤ (Z:ℝ)^13) (hL : (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ)) :
    R*(L:ℝ) ≤ (Z^14:ℕ) := by
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hLZ : (L:ℝ) ≤ Z := hL.trans (by
    calc
      (Z:ℝ)^(1/50:ℝ) ≤ (Z:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZr (by norm_num)
      _ = Z := Real.rpow_one _)
  calc
    R*(L:ℝ) ≤ (Z:ℝ)^13*(L:ℝ) := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg L)
    _ ≤ (Z:ℝ)^13*Z := mul_le_mul_of_nonneg_left hLZ (by positivity)
    _ = (Z^14:ℕ) := by push_cast; ring

theorem actual_array_mean_exponential_loss {K : ℝ} (hK : 3000 ≤ K) :
    Real.exp ((3/200:ℝ)*K) ≤ Real.exp ((2/125:ℝ)*K)/4 := by
  have he : (4:ℝ) ≤ Real.exp ((1/1000:ℝ)*K) := by
    have hh := Real.add_one_le_exp ((1/1000:ℝ)*K)
    linarith
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos ((3/200:ℝ)*K)).le
  rw [← Real.exp_add] at hm
  have hid : (3/200:ℝ)*K+(1/1000:ℝ)*K=(2/125:ℝ)*K := by ring
  rw [hid] at hm
  linarith

theorem eventually_actual_array_mean_exponential_loss :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      Real.exp ((3/200:ℝ)*auxiliaryK Z z) ≤
        Real.exp ((2/125:ℝ)*auxiliaryK Z z)/4 := by
  filter_upwards [eventually_auxiliaryK_bounds,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 3000]
    with T hK hT
  intro Z z hZl hZu hz hzl hzu
  exact actual_array_mean_exponential_loss (hT.trans (hK Z z hZl hZu hz hzl hzu).1)

end Ostmann.QuadraticCenter

end

end OAI
