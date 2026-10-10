import OAI.Geometry.TranslativeCovering.LocalizationComplete

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialIntegral
open Set MeasureTheory Metric
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma deficit_indicator {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    max (1-r^2/a^2) 0 = (Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r := by
  by_cases h : r < a
  · rw [indicator_of_mem (show r ∈ Iio a from h),max_eq_left]
    apply sub_nonneg.mpr
    exact (div_le_one (sq_pos_of_pos ha)).mpr ((sq_le_sq₀ hr ha.le).mpr h.le)
  · rw [indicator_of_notMem (show r ∉ Iio a from h),max_eq_right]
    apply sub_nonpos.mpr
    exact (one_le_div (sq_pos_of_pos ha)).mpr ((sq_le_sq₀ ha.le hr).mpr (le_of_not_gt h))

lemma polynomial_integral {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioo (0:ℝ) a,r^(n-1)*(1-r^2/a^2) = 2*a^n/((n:ℝ)*((n:ℝ)+2)) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ha.le]
  have he (r : ℝ) : r^(n-1)*(1-r^2/a^2) = r^(n-1)-r^(n+1)/a^2 := by
    rw [mul_sub,mul_one,← mul_div_assoc,← pow_add]
    rw [show n-1+2 = n+1 by omega]
  simp_rw [he]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),intervalIntegral.integral_div,
    integral_pow,integral_pow]
  have hn1 : n-1+1 = n := by omega
  rw [hn1]
  simp only [zero_pow (by omega : n ≠ 0),zero_pow (by omega : n+1+1 ≠ 0),sub_zero,
    Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 1 ≤ n by omega)]
  rw [show n+1+1 = n+2 by omega,pow_add]
  have hnp : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sub_add_cancel]
  field_simp
  ring

lemma deficit_integral {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 < a) :
    ∫ x : Space n,max (1-‖x‖^2/a^2) 0 =
      2/((n:ℝ)+2)*volume.real (closedBall (0 : Space n) a) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have : Nontrivial (Space n) := inferInstance
  have he (x : Space n) := deficit_indicator ha (norm_nonneg x)
  simp_rw [he]
  rw [integral_fun_norm_addHaar volume ((Iio a).indicator (fun r : ℝ => 1-r^2/a^2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin,nsmul_eq_mul,smul_eq_mul]
  have hinside : (∫ r in Ioi (0:ℝ),r^(n-1)*(Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r) =
      ∫ r in Ioo (0:ℝ) a,r^(n-1)*(1-r^2/a^2) := by
    have heq : (fun r : ℝ => r^(n-1)*(Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r) =
        (Iio a).indicator (fun r : ℝ => r^(n-1)*(1-r^2/a^2)) := by
      funext r
      by_cases hr : r ∈ Iio a <;> simp [hr]
    rw [heq]
    rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
    rw [show Iio a ∩ Ioi (0:ℝ) = Ioo 0 a by ext r; exact and_comm]
  rw [hinside,polynomial_integral hn ha]
  rw [volume.addHaar_real_closedBall _ ha.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  field_simp

end RadialIntegral

end OAI
