import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def RapidDecay (a : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Summable (fun n : ℕ => (n+1:ℝ)^m*a n)

lemma RapidDecay.of_le {a b : ℕ → ℝ} (hb : RapidDecay b) (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ᶠ n in atTop, a n ≤ b n) : RapidDecay a := by
  intro m
  apply (hb m).of_norm_bounded_eventually_nat
  filter_upwards [hle] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

lemma RapidDecay.add {a b : ℕ → ℝ} (ha : RapidDecay a) (hb : RapidDecay b) :
    RapidDecay (fun n : ℕ => a n+b n) := by
  intro m
  simpa only [mul_add] using (ha m).add (hb m)

lemma RapidDecay.const_mul {a : ℕ → ℝ} (ha : RapidDecay a) (c : ℝ) :
    RapidDecay (fun n : ℕ => c*a n) := by
  intro m
  simpa only [mul_left_comm] using (ha m).mul_left c

lemma RapidDecay.pow_mul {a : ℕ → ℝ} (ha : RapidDecay a) (k : ℕ) :
    RapidDecay (fun n : ℕ => (n+1:ℝ)^k*a n) := by
  intro m
  simpa only [pow_add,mul_assoc] using ha (m+k)

lemma RapidDecay.shift {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n) (k : ℕ) :
    RapidDecay (fun n : ℕ => a (n+k)) := by
  intro m
  apply ((summable_nat_add_iff k).mpr (ha m)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha0 _))]
  apply mul_le_mul_of_nonneg_right _ (ha0 _)
  exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) m

lemma rapidDecay_of_power_bounds {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : ∀ D : ℝ, 0 ≤ D → ∀ᶠ n : ℕ in atTop, a n ≤ (n:ℝ)^(-D)) : RapidDecay a := by
  intro m
  have hs : Summable (fun n : ℕ => (2:ℝ)^m*(n:ℝ)^(-2:ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ)< -1)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [h (m+2) (by positivity),eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  calc
    _ ≤ (2*(n:ℝ))^m*(n:ℝ)^(-(m+2:ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) m) hn (ha n) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_assoc,← Real.rpow_natCast (n:ℝ) m,← Real.rpow_add hn0]
      congr 1
      congr 1
      ring

lemma rapidDecay_of_weighted_limit {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : ∀ m : ℕ, Tendsto (fun n : ℕ => (n+1:ℝ)^m*a n) atTop (𝓝 0)) : RapidDecay a := by
  intro m
  have hs : Summable (fun n : ℕ => ((n+1:ℝ)^2)⁻¹) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by omega : 1<(2:ℕ)))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [(h (m+2)).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℝ)^2)).mpr
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using hn.le

lemma power_stretchedExp_limit (p q c : ℝ) (hq : 0<q) (hc : 0<c) :
    Tendsto (fun x : ℝ => x^p*Real.exp (-c*x^q)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/q) c hc).comp (tendsto_rpow_atTop hq)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  change (x^q)^(p/q)*Real.exp (-c*x^q)=_
  rw [← Real.rpow_mul hx]
  congr 2
  field_simp

lemma rapidDecay_stretchedExp (q c : ℝ) (hq : 0<q) (hc : 0<c) :
    RapidDecay (fun n : ℕ => Real.exp (-c*(n+1:ℝ)^q)) := by
  apply rapidDecay_of_weighted_limit (fun _ => (Real.exp_pos _).le)
  intro m
  have ht : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast,Function.comp_def] using (power_stretchedExp_limit m q c hq hc).comp ht

lemma rapidDecay_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r<1) : RapidDecay (fun n : ℕ => r^n) := by
  intro m
  have hs := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := r) m (by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)).mul_left ((2:ℝ)^m)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*(n:ℝ))^m*r^n := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) m) (pow_nonneg hr0 _)
    _ = _ := by rw [mul_pow,mul_assoc]

lemma descending_probability_bound (N : ℕ) :
    (1-((N+1:ℕ):ℝ)^(-(1/2:ℝ)))^(N+1) ≤
      Real.exp (-((N+1:ℕ):ℝ)^(1/2:ℝ)) := by
  have hn : (0:ℝ)<(N+1:ℕ) := by positivity
  have h1 : (1:ℝ)≤(N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have ha := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : -(1/2:ℝ)≤0)
  calc
    _ ≤ (Real.exp (-((N+1:ℕ):ℝ)^(-(1/2:ℝ))))^(N+1) :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-((N+1:ℕ):ℝ)^(1/2:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_neg]
      congr 1
      calc
        _ = ((N+1:ℕ):ℝ)^(1:ℝ)*((N+1:ℕ):ℝ)^(-(1/2:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

end DirectionalTransience

end

end OAI
