import Mathlib
import OAI.Probability.SKRatio.Gaussian.ExponentialEvents

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatioClock.Regression

lemma eventually_polynomial_exp_le {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^k*exp (-a*n) ≤ exp (-(a/2)*n) := by
  have ht : Tendsto (fun n : ℕ => (a/2)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const ((a/2)^k)
  simp only [zero_div] at h
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)^k*exp (-(a/2)*n)) atTop (𝓝 0) := by
    convert h using 1
    funext n
    simp only [Function.comp_apply,mul_pow,neg_mul]
    field_simp
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  calc
    _ = ((n:ℝ)^k*exp (-(a/2)*n))*exp (-(a/2)*n) := by
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ 1*exp (-(a/2)*n) := mul_le_mul_of_nonneg_right hn.le (by positivity)
    _ = _ := one_mul _

lemma eventually_geom_exp_quadratic_le {a b c : ℝ} (ha : 0<a) (hb : 0<b) :
    ∀ᶠ n : ℕ in atTop, b^n*exp (-a*(n:ℝ)^2) ≤ exp (-c*n) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [hn.eventually (eventually_ge_atTop ((log b+c)/a))] with n hn
  rw [show b^n = exp ((n:ℝ)*log b) by rw [exp_nat_mul,exp_log hb],←exp_add]
  apply exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hn) (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hh]

lemma exponentiallyRare_of_polynomial {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n))
    {C c : ℝ} (hC : 0<C) (hc : 0<c) (k : ℕ)
    (hbound : ∀ᶠ n in atTop, ρ n (A n) ≤ ENNReal.ofReal (C*(n:ℝ)^k*exp (-c*n))) :
    ExponentiallyRare ρ A := by
  refine ⟨C,c/2,hC,by positivity,?_⟩
  filter_upwards [hbound,eventually_polynomial_exp_le hc k] with n hn hp
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le

lemma exponentiallyRare_of_geom_quadratic {H : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n))
    {C a b : ℝ} (hC : 0<C) (ha : 0<a) (hb : 0<b)
    (hbound : ∀ᶠ n in atTop,
      ρ n (A n) ≤ ENNReal.ofReal (C*b^n*exp (-a*(n:ℝ)^2))) :
    ExponentiallyRare ρ A := by
  refine ⟨C,1,hC,by norm_num,?_⟩
  filter_upwards [hbound,eventually_geom_exp_quadratic_le (c := 1) ha hb] with n hn hp
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le

lemma exponentiallyRare_iUnion_polynomial {H I : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, Fintype (I n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, I n → Set (H n))
    {c C D : ℝ} (hc : 0<c) (hC : 0<C) (hD : 0<D) (k : ℕ)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n) : ℝ) ≤ D*(n:ℝ)^k)
    (hbound : ∀ᶠ n in atTop, ∀ i, ρ n (A n i) ≤ ENNReal.ofReal (C*exp (-c*n))) :
    ExponentiallyRare ρ (fun n => ⋃ i, A n i) := by
  apply exponentiallyRare_of_polynomial ρ _ (mul_pos hD hC) hc k
  filter_upwards [hcard,hbound] with n hcard hb
  calc
    _ ≤ ∑ i, ρ n (A n i) := measure_iUnion_fintype_le (ρ n) _
    _ ≤ ∑ _i : I n, ENNReal.ofReal (C*exp (-c*n)) := Finset.sum_le_sum (fun i _ => hb i)
    _ = ENNReal.ofReal ((Fintype.card (I n):ℝ)*(C*exp (-c*n))) := by
      simp [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((D*C)*(n:ℝ)^k*exp (-c*n)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (D*(n:ℝ)^k)*(C*exp (-c*n)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

end SKRatioClock.Regression

end
end

end OAI
