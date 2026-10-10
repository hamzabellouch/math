import OAI.MathematicalPhysics.CriticalSK.GaussianMoments

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

lemma chiSquare_mgf (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (chiSquare m) (standardGaussianProduct m) t =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ m := by
  unfold mgf chiSquare standardGaussianProduct
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (x : ℝ) => Real.exp (t * x ^ 2))]
  simp_rw [gaussian_square_integral t ht]
  simp

lemma chiSquare_exp_integrable (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x => Real.exp (t * chiSquare m x)) (standardGaussianProduct m) := by
  apply mgf_pos_iff.mp
  rw [chiSquare_mgf m t ht]
  exact pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))) m

lemma chiSquare_mgf_exp (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (chiSquare m) (standardGaussianProduct m) t =
      Real.exp (-(m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  rw [chiSquare_mgf m t ht]
  have hb : 0 < 1 - 2 * t := by linarith
  rw [← Real.exp_log (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)) m),
    Real.log_pow, Real.log_inv, Real.log_sqrt hb.le]
  congr 1
  ring

lemma chiSquare_chernoff_value (m : ℕ) (a : ℝ) (ha : 0 < a) :
    Real.exp (-((1 - a⁻¹) / 2) * (m * a)) *
      mgf (chiSquare m) (standardGaussianProduct m) ((1 - a⁻¹) / 2) =
    Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha; linarith
  rw [chiSquare_mgf_exp m _ ht, ← Real.exp_add]
  have he : 1 - 2 * ((1 - a⁻¹) / 2) = a⁻¹ := by ring
  rw [he, Real.log_inv]
  congr 1
  field_simp
  ring

lemma chiSquare_upper_tail (m : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    (standardGaussianProduct m).real {x | (m : ℝ) * a ≤ chiSquare m x} ≤
      Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ha0 : 0 < a := by linarith
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha0; linarith
  have ht0 : 0 ≤ (1 - a⁻¹) / 2 := by
    have := inv_le_one₀ ha0 |>.mpr ha
    linarith
  have hh := measure_ge_le_exp_mul_mgf (μ := standardGaussianProduct m)
    (X := chiSquare m) ((m : ℝ) * a) ht0 (chiSquare_exp_integrable m _ ht)
  simpa only [chiSquare_chernoff_value m a ha0] using hh

lemma chiSquare_lower_tail (m : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (standardGaussianProduct m).real {x | chiSquare m x ≤ (m : ℝ) * a} ≤
      Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha; linarith
  have ht0 : (1 - a⁻¹) / 2 ≤ 0 := by
    have := one_le_inv₀ ha |>.mpr ha1
    linarith
  have hh := measure_le_le_exp_mul_mgf (μ := standardGaussianProduct m)
    (X := chiSquare m) ((m : ℝ) * a) ht0 (chiSquare_exp_integrable m _ ht)
  simpa only [chiSquare_chernoff_value m a ha] using hh

lemma chi_entropy_lower (a : ℝ) (ha : 0 < a) :
    (Real.sqrt a - 1) ^ 2 ≤ a - 1 - Real.log a := by
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ha)
  rw [Real.log_sqrt ha.le] at hh
  nlinarith [Real.sq_sqrt ha.le]

lemma chiSquare_nonneg (m : ℕ) (x : Fin m → ℝ) : 0 ≤ chiSquare m x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma chiSquare_eq_zero_iff (m : ℕ) (x : Fin m → ℝ) : chiSquare m x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hle : x i ^ 2 ≤ chiSquare m x := Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
    rw [hx] at hle
    simpa using sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  · rintro rfl
    simp [chiSquare]

lemma chiSquare_zero_measure (m : ℕ) (hm : 0 < m) :
    standardGaussianProduct m {x | chiSquare m x = 0} = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  simp only [chiSquare_eq_zero_iff, Set.ofPred_eq_eq_singleton, standardGaussianProduct,
    measure_singleton]

lemma chi_radius_algebra (m : ℕ) (hm : 0 < m) (u : ℝ) :
    (m : ℝ) * (u / Real.sqrt m) ^ 2 = u ^ 2 ∧
    (m : ℝ) / 2 * (u / Real.sqrt m - 1) ^ 2 = (u - Real.sqrt m) ^ 2 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb0 : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  have hb := Real.sq_sqrt hm0.le
  constructor
  · rw [div_pow, hb]
    field_simp
  · rw [div_sub_one hb0, div_pow, hb]
    field_simp

lemma chi_upper_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | Real.sqrt m + r ≤ Real.sqrt (chiSquare m x)} ≤
      Real.exp (-r ^ 2 / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  let u := Real.sqrt (m : ℝ) + r
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : 1 ≤ u / Real.sqrt (m : ℝ) := (le_div_iff₀ hb).mpr (by dsimp [u]; linarith)
  have ha : 1 ≤ (u / Real.sqrt (m : ℝ)) ^ 2 := by nlinarith
  have halg := chi_radius_algebra m hm u
  calc
    _ ≤ (standardGaussianProduct m).real {x | (m : ℝ) * (u / Real.sqrt m) ^ 2 ≤ chiSquare m x} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro x hx
      rw [halg.1]
      have hsq := Real.sq_sqrt (chiSquare_nonneg m x)
      change u ≤ _ at hx
      change u ^ 2 ≤ chiSquare m x
      nlinarith [sq_le_sq₀ hu.le (Real.sqrt_nonneg (chiSquare m x)) |>.mpr hx]
    _ ≤ Real.exp (-(m : ℝ) / 2 * ((u / Real.sqrt m) ^ 2 - 1 - Real.log ((u / Real.sqrt m) ^ 2))) :=
      chiSquare_upper_tail m _ ha
    _ ≤ Real.exp (-r ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have he := chi_entropy_lower ((u / Real.sqrt m) ^ 2) (lt_of_lt_of_le zero_lt_one ha)
      rw [Real.sqrt_sq (by positivity)] at he
      have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ m / 2 by positivity)
      rw [halg.2] at hh
      dsimp [u] at hh
      nlinarith

lemma chi_lower_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} ≤
      Real.exp (-r ^ 2 / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  by_cases hru : r < Real.sqrt (m : ℝ)
  · let u := Real.sqrt (m : ℝ) - r
    have hu : 0 < u := by dsimp [u]; linarith
    have hu1 : u / Real.sqrt (m : ℝ) ≤ 1 := (div_le_one hb).mpr (by dsimp [u]; linarith)
    have hur : 0 < u / Real.sqrt (m : ℝ) := div_pos hu hb
    have ha : (u / Real.sqrt (m : ℝ)) ^ 2 ≤ 1 := by nlinarith
    have ha0 : 0 < (u / Real.sqrt (m : ℝ)) ^ 2 := sq_pos_of_pos hur
    have halg := chi_radius_algebra m hm u
    calc
      _ ≤ (standardGaussianProduct m).real {x | chiSquare m x ≤ (m : ℝ) * (u / Real.sqrt m) ^ 2} := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        rw [halg.1]
        have hsq := Real.sq_sqrt (chiSquare_nonneg m x)
        change _ ≤ u at hx
        change chiSquare m x ≤ u ^ 2
        nlinarith [sq_le_sq₀ (Real.sqrt_nonneg (chiSquare m x)) hu.le |>.mpr hx]
      _ ≤ Real.exp (-(m : ℝ) / 2 * ((u / Real.sqrt m) ^ 2 - 1 - Real.log ((u / Real.sqrt m) ^ 2))) :=
        chiSquare_lower_tail m _ ha0 ha
      _ ≤ Real.exp (-r ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have he := chi_entropy_lower ((u / Real.sqrt m) ^ 2) ha0
        rw [Real.sqrt_sq hur.le] at he
        have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ m / 2 by positivity)
        rw [halg.2] at hh
        dsimp [u] at hh
        nlinarith
  · have hzero : (standardGaussianProduct m).real
        {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} = 0 := by
      apply measureReal_mono_null (s₂ := {x | chiSquare m x = 0})
      · intro x hx
        have hn : 0 ≤ Real.sqrt (chiSquare m x) := Real.sqrt_nonneg _
        have hz : Real.sqrt (chiSquare m x) = 0 := by dsimp at hx; linarith
        exact (Real.sqrt_eq_zero (chiSquare_nonneg m x)).mp hz
      · simp [Measure.real, chiSquare_zero_measure m hm]
    rw [hzero]
    positivity

lemma chi_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | r ≤ |Real.sqrt (chiSquare m x) - Real.sqrt m|} ≤
      2 * Real.exp (-r ^ 2 / 2) := by
  have hset : {x | r ≤ |Real.sqrt (chiSquare m x) - Real.sqrt m|} =
      {x | Real.sqrt m + r ≤ Real.sqrt (chiSquare m x)} ∪
      {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor <;> intro h <;> rcases h with h | h <;> first | left; linarith | right; linarith
  rw [hset]
  exact (measureReal_union_le _ _).trans (by
    have := chi_upper_tail m hm r hr
    have := chi_lower_tail m hm r hr
    linarith)

def chi (m : ℕ) (x : Fin m → ℝ) : ℝ := Real.sqrt (chiSquare m x)

lemma chi_measurable (m : ℕ) : Measurable (chi m) := by
  unfold chi chiSquare
  fun_prop

lemma chi_sq (m : ℕ) (x : Fin m → ℝ) : chi m x ^ 2 = chiSquare m x :=
  Real.sq_sqrt (chiSquare_nonneg m x)

lemma chiSquare_integrable (m : ℕ) : Integrable (chiSquare m) (standardGaussianProduct m) := by
  simpa using integrable_pow_of_integrable_exp_mul (X := chiSquare m)
    (by norm_num : (1 / 4 : ℝ) ≠ 0) (chiSquare_exp_integrable m _ (by norm_num))
    (chiSquare_exp_integrable m _ (by norm_num)) 1

lemma chi_integrable (m : ℕ) : Integrable (chi m) (standardGaussianProduct m) := by
  change Integrable (fun x => Real.sqrt (chiSquare m x)) _
  simpa only [Real.sqrt_eq_rpow] using integrable_rpow_of_integrable_exp_mul
    (X := chiSquare m) (by norm_num : (1 / 4 : ℝ) ≠ 0)
    (chiSquare_exp_integrable m _ (by norm_num))
    (chiSquare_exp_integrable m _ (by norm_num)) (p := 1 / 2) (by norm_num)

lemma chi_memLp_two (m : ℕ) : MemLp (chi m) 2 (standardGaussianProduct m) := by
  rw [memLp_two_iff_integrable_sq (chi_measurable m).aestronglyMeasurable]
  simpa only [chi_sq] using chiSquare_integrable m

lemma chi_center_integrable_sq (m : ℕ) (c : ℝ) :
    Integrable (fun x => (chi m x - c) ^ 2) (standardGaussianProduct m) := by
  have h := (chi_memLp_two m).sub (memLp_const c)
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h

lemma chi_mean_square_error (m : ℕ) (hm : 0 < m) :
    (∫ x, (chi m x - Real.sqrt m) ^ 2 ∂standardGaussianProduct m) ≤ 4 := by
  rw [(chi_center_integrable_sq m (Real.sqrt m)).integral_eq_integral_meas_le
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  have hbound : ∀ t : ℝ, 0 < t → (standardGaussianProduct m).real
      {x | t ≤ (chi m x - Real.sqrt m) ^ 2} ≤ 2 * Real.exp (-(1 / 2) * t) := by
    intro t ht
    have hset : {x | t ≤ (chi m x - Real.sqrt m) ^ 2} =
        {x | Real.sqrt t ≤ |chi m x - Real.sqrt m|} := by
      ext x
      simp only [Set.mem_ofPred_eq, Real.sqrt_le_iff, abs_nonneg, true_and, sq_abs]
    rw [hset]
    have h := chi_tail m hm (Real.sqrt t) (Real.sqrt_nonneg t)
    simpa [chi, Real.sq_sqrt ht.le, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using h
  calc
    _ ≤ ∫ t in Set.Ioi 0, 2 * Real.exp (-(1 / 2) * t) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => measureReal_nonneg)
      · exact (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0).const_mul 2
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hbound t ht
    _ = 4 := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0)]
      norm_num

lemma gaussian_integral_square : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (μ := gaussianReal 0 1) (X := id) (memLp_id_gaussianReal 2)
  simpa only [variance_id_gaussianReal, NNReal.coe_one, id_eq, Pi.pow_apply,
    integral_id_gaussianReal, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

lemma chiSquare_mean (m : ℕ) :
    (∫ x, chiSquare m x ∂standardGaussianProduct m) = m := by
  have hg : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    simpa using (memLp_two_iff_integrable_sq
      (measurable_id.aestronglyMeasurable : AEStronglyMeasurable id (gaussianReal 0 1))).mp
        (memLp_id_gaussianReal 2)
  unfold chiSquare standardGaussianProduct
  rw [integral_finsetSum Finset.univ (f := fun (i : Fin m) (x : Fin m → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i) hg)]
  have hcomp (i : Fin m) :
      (∫ x : Fin m → ℝ, x i ^ 2 ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = 1 := by
    rw [integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i)
      hg.aestronglyMeasurable]
    exact gaussian_integral_square
  simp only [hcomp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma chi_mean_nonneg (m : ℕ) : 0 ≤ ∫ x, chi m x ∂standardGaussianProduct m :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

lemma chi_mean_upper (m : ℕ) : (∫ x, chi m x ∂standardGaussianProduct m) ≤ Real.sqrt m := by
  have hv := variance_nonneg (X := chi m) (μ := standardGaussianProduct m)
  rw [variance_eq_sub (chi_memLp_two m)] at hv
  simp only [Pi.pow_apply, chi_sq, chiSquare_mean] at hv
  exact (Real.le_sqrt (chi_mean_nonneg m) (Nat.cast_nonneg m)).mpr (by linarith)

lemma chi_mean_bias (m : ℕ) (hm : 0 < m) :
    0 ≤ Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ∧
      Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ≤ 2 / Real.sqrt m := by
  refine ⟨sub_nonneg.mpr (chi_mean_upper m), ?_⟩
  have he := chi_mean_square_error m hm
  have hpoint : (fun x => (chi m x - Real.sqrt m) ^ 2) =
      (fun x => chiSquare m x - 2 * Real.sqrt m * chi m x + (m : ℝ)) := by
    funext x
    rw [sub_sq, chi_sq, Real.sq_sqrt (Nat.cast_nonneg m)]
    ring
  rw [hpoint, integral_add (f := fun x => chiSquare m x - 2 * Real.sqrt m * chi m x)
    (g := fun _ => (m : ℝ)) ((chiSquare_integrable m).sub
    ((chi_integrable m).const_mul _)) (integrable_const _),
    integral_sub (f := chiSquare m) (g := fun x => 2 * Real.sqrt m * chi m x)
      (chiSquare_integrable m) ((chi_integrable m).const_mul _),
    integral_const_mul, chiSquare_mean, integral_const] at he
  simp only [probReal_univ, smul_eq_mul, one_mul] at he
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm))).mpr
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)]

lemma chi_square_deviation_tail (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    (standardGaussianProduct m).real {x | t ≤ (chi m x - Real.sqrt m) ^ 2} ≤
      2 * Real.exp (-(1 / 2) * t) := by
  have hset : {x | t ≤ (chi m x - Real.sqrt m) ^ 2} =
      {x | Real.sqrt t ≤ |chi m x - Real.sqrt m|} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_le_iff, abs_nonneg, true_and, sq_abs]
  rw [hset]
  simpa [chi, Real.sq_sqrt ht, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using
    chi_tail m hm (Real.sqrt t) (Real.sqrt_nonneg t)

lemma chi_square_deviation_exp_integrable (m : ℕ) :
    Integrable (fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4))
      (standardGaussianProduct m) := by
  apply ((chiSquare_exp_integrable m (1 / 4) (by norm_num)).const_mul
    (Real.exp ((m : ℝ) / 4))).mono'
  · exact ((chi_measurable m).sub measurable_const).pow_const 2 |>.div_const 4 |>.exp
      |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := Real.sqrt_nonneg (chiSquare m x)
    have h2 := Real.sqrt_nonneg (m : ℝ)
    have h3 := chi_sq m x
    have h4 := Real.sq_sqrt (Nat.cast_nonneg m)
    change 0 ≤ chi m x at h1
    nlinarith [mul_nonneg h1 h2]

lemma chi_square_deviation_exp_bound (m : ℕ) (hm : 0 < m) :
    (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
      ∂standardGaussianProduct m) ≤ 3 := by
  have hi := chi_square_deviation_exp_integrable m
  have hnonneg : ∀ x, 0 ≤ Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1 := by
    intro x
    exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hformula (u : ℝ) : (∫ t in (0 : ℝ)..u, (1 / 4 : ℝ) * Real.exp (t / 4)) =
      Real.exp (u / 4) - 1 := by
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t / 4))
        ((1 / 4 : ℝ) * Real.exp (x / 4)) x := by
      simpa only [id_eq, one_div, mul_comm] using ((hasDerivAt_id x).div_const 4).exp
    simpa only [zero_div, Real.exp_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        ((by fun_prop : Continuous (fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4))).intervalIntegrable 0 u)
  have hl := lintegral_comp_eq_lintegral_meas_le_mul
    (f := fun x => (chi m x - Real.sqrt m) ^ 2)
    (g := fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4)) (standardGaussianProduct m)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (((chi_measurable m).sub measurable_const).pow_const 2).aemeasurable
    (fun t _ => (by fun_prop : Continuous (fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4))).intervalIntegrable 0 t)
    (Filter.Eventually.of_forall (fun _ => by positivity))
  simp_rw [hformula] at hl
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1) (hi.sub (integrable_const 1))
    (Filter.Eventually.of_forall hnonneg)] at hl
  have hb : ENNReal.ofReal (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1
      ∂standardGaussianProduct m) ≤ ENNReal.ofReal 2 := by
    rw [hl]
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-(1 / 4) * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (2 * Real.exp (-(1 / 2) * t)) * ((1 / 4) * Real.exp (t / 4)) := by
            gcongr
            exact chi_square_deviation_tail m hm t ht.le
          _ = (1 / 2) * Real.exp (-(1 / 4) * t) := by
            rw [show -(1 / 4) * t = -(1 / 2) * t + t / 4 by ring, Real.exp_add]
            ring
      _ = ENNReal.ofReal 2 := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) 0).const_mul (1 / 2))
          (Filter.Eventually.of_forall (fun _ => by positivity))]
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0)]
        norm_num
  have hb' := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hb
  rw [integral_sub (f := fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4))
    (g := fun _ => (1 : ℝ)) hi (integrable_const 1)] at hb'
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb'
  linarith

lemma exp_quadratic_remainder (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h : |Real.exp x - (1 + x)| ≤ x ^ 2 * Real.exp |x| := by
    have hc := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
    norm_num [Finset.sum_range_succ] at hc
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hc
  have hh := (abs_le.mp h).2
  linarith

lemma exp_quadratic_domination (t z : ℝ) :
    Real.exp (t * z) ≤ 1 + t * z +
      (16 * t ^ 2 * Real.exp (4 * t ^ 2)) * Real.exp (z ^ 2 / 8) := by
  have hy : |t * z| ≤ 4 * t ^ 2 + z ^ 2 / 16 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (2 * t + z / 4), sq_nonneg (2 * t - z / 4)]
  have hz : z ^ 2 ≤ 16 * Real.exp (z ^ 2 / 16) := by
    have := Real.add_one_le_exp (z ^ 2 / 16)
    linarith
  calc
    _ ≤ 1 + t * z + (t * z) ^ 2 * Real.exp |t * z| := exp_quadratic_remainder _
    _ ≤ 1 + t * z + (t * z) ^ 2 * Real.exp (4 * t ^ 2 + z ^ 2 / 16) := by gcongr
    _ = 1 + t * z + (t ^ 2 * Real.exp (4 * t ^ 2)) * (z ^ 2 * Real.exp (z ^ 2 / 16)) := by
      rw [Real.exp_add]
      ring
    _ ≤ 1 + t * z + (t ^ 2 * Real.exp (4 * t ^ 2)) *
        (16 * Real.exp (z ^ 2 / 16) * Real.exp (z ^ 2 / 16)) := by gcongr
    _ = _ := by
      rw [show z ^ 2 / 8 = z ^ 2 / 16 + z ^ 2 / 16 by ring, Real.exp_add]
      ring

lemma one_add_linear_mul_exp_le (a b r : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    1 + a * r * Real.exp (b * r) ≤ Real.exp ((a + b) * r) := by
  calc
    _ ≤ Real.exp (b * r) + a * r * Real.exp (b * r) := by
      gcongr
      exact Real.one_le_exp (mul_nonneg hb hr)
    _ = (1 + a * r) * Real.exp (b * r) := by ring
    _ ≤ Real.exp (a * r) * Real.exp (b * r) := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp (a * r)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma centered_mgf_from_exp_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hX : Integrable X μ) (hzero : ∫ x, X x ∂μ = 0)
    (hexp : Integrable (fun x => Real.exp (X x ^ 2 / 8)) μ)
    (hB : (∫ x, Real.exp (X x ^ 2 / 8) ∂μ) ≤ B) (hB0 : 0 ≤ B) (t : ℝ) :
    (∫ x, Real.exp (t * X x) ∂μ) ≤ Real.exp ((16 * B + 4) * t ^ 2) := by
  have hbound := fun x => exp_quadratic_domination t (X x)
  calc
    _ ≤ ∫ x, (1 + t * X x) + (16 * t ^ 2 * Real.exp (4 * t ^ 2)) *
        Real.exp (X x ^ 2 / 8) ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
      · exact ((integrable_const 1).add (hX.const_mul t)).add (hexp.const_mul _)
      · exact Filter.Eventually.of_forall hbound
    _ = 1 + (16 * t ^ 2 * Real.exp (4 * t ^ 2)) *
        (∫ x, Real.exp (X x ^ 2 / 8) ∂μ) := by
      rw [integral_add (f := fun x => 1 + t * X x)
        (g := fun x => (16 * t ^ 2 * Real.exp (4 * t ^ 2)) * Real.exp (X x ^ 2 / 8))
        ((integrable_const 1).add (hX.const_mul t)) (hexp.const_mul _),
        integral_add (f := fun _ => (1 : ℝ)) (g := fun x => t * X x)
        (integrable_const 1) (hX.const_mul t), integral_const_mul, integral_const_mul, hzero]
      simp
    _ ≤ 1 + (16 * B) * (t ^ 2) * Real.exp (4 * t ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hB
        (show 0 ≤ 16 * t ^ 2 * Real.exp (4 * t ^ 2) by positivity)]
    _ ≤ _ := one_add_linear_mul_exp_le (16 * B) 4 (t ^ 2) (by positivity) (by norm_num) (sq_nonneg t)

lemma integrable_exp_of_exp_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ)
    (hexp : Integrable (fun x => Real.exp (X x ^ 2 / 8)) μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * X x)) μ := by
  apply (hexp.const_mul (Real.exp (4 * t ^ 2))).mono'
  · exact Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul t)
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (2 * t - X x / 4), sq_nonneg (X x)]

lemma chi_bias_le_two (m : ℕ) (hm : 0 < m) :
    Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ≤ 2 := by
  have hs : (1 : ℝ) ≤ Real.sqrt m := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt this
  calc
    _ ≤ 2 / Real.sqrt m := (chi_mean_bias m hm).2
    _ ≤ 2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith

lemma chi_center_square_exp_pointwise (m : ℕ) (hm : 0 < m) (x : Fin m → ℝ) :
    Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8) ≤
      Real.exp 1 * Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb0 := (chi_mean_bias m hm).1
  have hb2 := chi_bias_le_two m hm
  have hb4 : (Real.sqrt m - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 ≤ 4 := by
    nlinarith
  nlinarith [sq_nonneg (chi m x - Real.sqrt m -
    (Real.sqrt m - (∫ y, chi m y ∂standardGaussianProduct m)))]

lemma chi_center_square_exp_integrable (m : ℕ) (hm : 0 < m) :
    Integrable (fun x => Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8))
      (standardGaussianProduct m) := by
  apply ((chi_square_deviation_exp_integrable m).const_mul (Real.exp 1)).mono'
  · exact ((chi_measurable m).sub measurable_const).pow_const 2 |>.div_const 8 |>.exp
      |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact chi_center_square_exp_pointwise m hm x

lemma chi_center_square_exp_bound (m : ℕ) (hm : 0 < m) :
    (∫ x, Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8)
      ∂standardGaussianProduct m) ≤ 3 * Real.exp 1 := by
  calc
    _ ≤ ∫ x, Real.exp 1 * Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
        ∂standardGaussianProduct m := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
      · exact (chi_square_deviation_exp_integrable m).const_mul (Real.exp 1)
      · exact Filter.Eventually.of_forall (chi_center_square_exp_pointwise m hm)
    _ = Real.exp 1 * (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
        ∂standardGaussianProduct m) := integral_const_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (chi_square_deviation_exp_bound m hm) (Real.exp_pos 1).le
      nlinarith

theorem chi_centered_subGaussian (m : ℕ) (hm : 0 < m) :
    HasSubgaussianMGF (fun x => chi m x - (∫ y, chi m y ∂standardGaussianProduct m))
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩ (standardGaussianProduct m) := by
  have hi : Integrable (fun x => chi m x - (∫ y, chi m y ∂standardGaussianProduct m))
      (standardGaussianProduct m) := (chi_integrable m).sub (integrable_const _)
  have hz : (∫ x, chi m x - (∫ y, chi m y ∂standardGaussianProduct m)
      ∂standardGaussianProduct m) = 0 := by
    rw [integral_sub (f := chi m) (g := fun _ => (∫ y, chi m y ∂standardGaussianProduct m))
      (chi_integrable m) (integrable_const _)]
    simp
  refine ⟨integrable_exp_of_exp_square hi.aestronglyMeasurable
    (chi_center_square_exp_integrable m hm), ?_⟩
  intro t
  have h := centered_mgf_from_exp_square hi hz (chi_center_square_exp_integrable m hm)
    (chi_center_square_exp_bound m hm) (by positivity) t
  change _ ≤ Real.exp ((2 * (48 * Real.exp 1 + 4)) * t ^ 2 / 2)
  convert h using 1
  congr 1
  ring_nf

def chiRowDim (n i : ℕ) : ℕ := max 1 (n - i)

abbrev ChiRows (n : ℕ) := (i : ℕ) → (Fin (chiRowDim n i) → ℝ)

def chiRowLaw (n : ℕ) : Measure (ChiRows n) :=
  Measure.infinitePi (fun i => standardGaussianProduct (chiRowDim n i))

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

def centeredChiRow (n i : ℕ) (ω : ChiRows n) : ℝ :=
  chi (chiRowDim n i) (ω i) - ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)

lemma centeredChiRow_measurable (n i : ℕ) : Measurable (centeredChiRow n i) :=
  ((chi_measurable _).comp (measurable_pi_apply i)).sub measurable_const

lemma centeredChiRows_independent (n : ℕ) : iIndepFun (centeredChiRow n) (chiRowLaw n) := by
  exact iIndepFun_infinitePi (fun i => (chi_measurable _).sub measurable_const)

lemma centeredChiRow_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (centeredChiRow n i)
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩ (chiRowLaw n) := by
  have h := chi_centered_subGaussian (chiRowDim n i) (by unfold chiRowDim; omega)
  have h' : HasSubgaussianMGF
      (fun x => chi (chiRowDim n i) x -
        ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i))
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩
      ((chiRowLaw n).map (fun ω => ω i)) := by
    simpa only [chiRowLaw, Measure.infinitePi_map_eval] using h
  exact HasSubgaussianMGF.of_map (μ := chiRowLaw n) (Y := fun ω : ChiRows n => ω i)
    (measurable_pi_apply i).aemeasurable h'

lemma centeredChiRow_mean (n i : ℕ) : (∫ ω, centeredChiRow n i ω ∂chiRowLaw n) = 0 := by
  let f (x : Fin (chiRowDim n i) → ℝ) := chi (chiRowDim n i) x -
    ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)
  have he := integral_map (μ := chiRowLaw n) (φ := fun ω : ChiRows n => ω i)
    (f := f) (measurable_pi_apply i).aemeasurable
    ((chi_measurable _).sub measurable_const).aestronglyMeasurable
  change (∫ ω, f (ω i) ∂chiRowLaw n) = 0
  rw [← he]
  simp only [chiRowLaw, Measure.infinitePi_map_eval]
  dsimp only [f]
  rw [integral_sub (chi_integrable _) (integrable_const _)]
  simp

def scaledChiRow (n i : ℕ) (ω : ChiRows n) : ℝ :=
  (Real.sqrt (n + 1))⁻¹ * centeredChiRow n i ω

lemma scaledChiRow_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (scaledChiRow n i)
      ⟨2 * (48 * Real.exp 1 + 4) / (n + 1), by positivity⟩ (chiRowLaw n) := by
  have h := (centeredChiRow_subGaussian n i).const_mul (Real.sqrt (n + 1))⁻¹
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  have ht := h.mgf_le t
  convert ht using 1
  congr 1
  apply congrArg Real.exp
  change (2 * (48 * Real.exp 1 + 4) / (n + 1)) * t ^ 2 / 2 =
    ((Real.sqrt (n + 1))⁻¹ ^ 2 * (2 * (48 * Real.exp 1 + 4))) * t ^ 2 / 2
  rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)]
  ring

lemma scaledChiRows_independent (n : ℕ) : iIndepFun (scaledChiRow n) (chiRowLaw n) :=
  (centeredChiRows_independent n).comp (fun _ x => (Real.sqrt (n + 1))⁻¹ * x)
    (fun _ => measurable_const.mul measurable_id)

lemma scaledChiRow_measurable (n i : ℕ) : Measurable (scaledChiRow n i) :=
  (centeredChiRow_measurable n i).const_mul _

lemma scaledChiRow_mean (n i : ℕ) : (∫ ω, scaledChiRow n i ω ∂chiRowLaw n) = 0 := by
  change (∫ ω, (Real.sqrt (n + 1))⁻¹ * centeredChiRow n i ω ∂chiRowLaw n) = 0
  rw [integral_const_mul, centeredChiRow_mean, mul_zero]

def diagonalMarginal (n _i : ℕ) : Measure ℝ :=
  gaussianReal 0 ⟨2 / (n + 1), by positivity⟩

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

def diagonalLaw (n : ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (diagonalMarginal n)

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

lemma gaussian_id_subGaussian (v : ℝ≥0) : HasSubgaussianMGF id v (gaussianReal 0 v) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_gaussianReal (μ := 0) (v := v) (by simp)]
  simp

lemma diagonalRows_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω i) ⟨2 / (n + 1), by positivity⟩ (diagonalLaw n) := by
  have h : HasSubgaussianMGF id ⟨2 / (n + 1), by positivity⟩
      ((diagonalLaw n).map (fun ω => ω i)) := by
    simpa only [diagonalLaw, Measure.infinitePi_map_eval, diagonalMarginal] using
      gaussian_id_subGaussian ⟨2 / (n + 1), by positivity⟩
  exact HasSubgaussianMGF.of_map (μ := diagonalLaw n) (Y := fun ω : ℕ → ℝ => ω i)
    (measurable_pi_apply i).aemeasurable h

lemma diagonalRows_independent (n : ℕ) :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (diagonalLaw n) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

lemma diagonalRows_mean (n i : ℕ) : (∫ ω, ω i ∂diagonalLaw n) = 0 := by
  have he := integral_map (μ := diagonalLaw n) (φ := fun ω : ℕ → ℝ => ω i)
    (f := id) (measurable_pi_apply i).aemeasurable (measurable_id.aestronglyMeasurable)
  change (∫ ω, id (ω i) ∂diagonalLaw n) = 0
  rw [← he]
  simp only [diagonalLaw, Measure.infinitePi_map_eval, diagonalMarginal]
  exact integral_id_gaussianReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma independent_product_submartingale {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hind : iIndepFun Y μ)
    (hint : ∀ n, Integrable (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) μ)
    (hi : ∀ i, Integrable (Y i) μ) (hpos : ∀ i ω, 0 ≤ Y i ω)
    (hmean : ∀ i, 1 ≤ ∫ ω, Y i ω ∂μ) :
    Submartingale (fun n ω => ∏ i ∈ Finset.range (n + 1), Y i ω)
      (Filtration.natural Y hY) μ := by
  have hadp : StronglyAdapted (Filtration.natural Y hY)
      (fun n ω => ∏ i ∈ Finset.range (n + 1), Y i ω) := by
    intro n
    have hh : ∀ i ∈ Finset.range (n + 1),
        StronglyMeasurable[Filtration.natural Y hY n] (Y i) := by
      intro i hi
      exact (Filtration.stronglyAdapted_natural hY i).mono
        ((Filtration.natural Y hY).mono (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    convert Finset.stronglyMeasurable_prod (Finset.range (n + 1)) hh using 1
    ext ω
    simp only [Finset.prod_apply]
  apply submartingale_nat hadp hint
  intro n
  have hid : (fun ω => ∏ i ∈ Finset.range (n + 1 + 1), Y i ω) =
      (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) * Y (n + 1) := by
    funext ω
    simp [Finset.prod_range_succ]
  rw [hid]
  have hcond := condExp_mul_of_stronglyMeasurable_left (hadp n)
    (hid ▸ hint (n + 1)) (hi (n + 1))
  have hindcond := hind.condExp_natural_ae_eq_of_lt hY (Nat.lt_succ_self n)
  filter_upwards [hcond, hindcond] with ω hc he
  rw [hc]
  simp only [Pi.mul_apply]
  rw [he]
  exact le_mul_of_one_le_right
    (Finset.prod_nonneg (fun i _ => hpos i ω)) (hmean (n + 1))

lemma exp_partial_sum_submartingale {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (t : ℝ) :
    ∃ (F : Filtration ℕ ‹MeasurableSpace Ω›),
      Submartingale (fun n ω => Real.exp (t * ∑ i ∈ Finset.range (n + 1), X i ω)) F μ := by
  let Y : ℕ → Ω → ℝ := fun i ω => Real.exp (t * X i ω)
  have hY : ∀ i, StronglyMeasurable (Y i) := fun i =>
    Real.continuous_exp.comp_stronglyMeasurable ((hX i).const_mul t)
  have hYi : ∀ i, Integrable (Y i) μ := fun i => (hmgf i).integrable_exp_mul t
  have hindY : iIndepFun Y μ := hind.comp (fun _ x => Real.exp (t * x))
    (fun _ => Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have heq (n : ℕ) : (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) =
      (fun ω => Real.exp (t * ∑ i ∈ Finset.range (n + 1), X i ω)) := by
    funext ω
    simp only [Y, Finset.mul_sum, Real.exp_sum]
  have hint (n : ℕ) : Integrable (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) μ := by
    rw [heq]
    exact (HasSubgaussianMGF.sum_of_iIndepFun hind (fun i _ => hmgf i)).integrable_exp_mul t
  have hm (i : ℕ) : 1 ≤ ∫ ω, Y i ω ∂μ := by
    have h := integral_mono (((hmgf i).integrable.const_mul t).add (integrable_const 1))
      (hYi i) (fun ω => Real.add_one_le_exp (t * X i ω))
    change (∫ ω, t * X i ω + 1 ∂μ) ≤ ∫ ω, Y i ω ∂μ at h
    rw [integral_add ((hmgf i).integrable.const_mul t) (integrable_const 1),
      integral_const_mul, hmean i] at h
    simpa using h
  refine ⟨Filtration.natural Y hY, ?_⟩
  have h := independent_product_submartingale hY hindY hint hYi
    (fun i ω => (Real.exp_pos _).le) hm
  convert h using 1
  funext n
  exact (heq n).symm

lemma partial_sum_maximal_exponential {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (m : ℕ) {a t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp (-t * a + (m + 1) * (c : ℝ) * t ^ 2 / 2) := by
  obtain ⟨F, hs⟩ := exp_partial_sum_submartingale hX hind hmgf hmean t
  let f : ℕ → Ω → ℝ := fun k ω => Real.exp (t * ∑ i ∈ Finset.range (k + 1), X i ω)
  let A : Set Ω := {ω | Real.exp (t * a) ≤
    (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one (fun k => f k ω)}
  have hmax := maximal_ineq (f := f) hs (fun k ω => (Real.exp_pos _).le)
    (ε := ⟨Real.exp (t * a), (Real.exp_pos _).le⟩) m
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hn : 0 ≤ ∫ ω in A, f m ω ∂μ := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hr' : Real.exp (t * a) * μ.real A ≤ ∫ ω in A, f m ω ∂μ := by
    rw [ENNReal.toReal_mul] at hr
    change Real.exp (t * a) * μ.real A ≤
      (ENNReal.ofReal (∫ ω in A, f m ω ∂μ)).toReal at hr
    rwa [ENNReal.toReal_ofReal hn] at hr
  have hsubset : {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ⊆ A := by
    rintro ω ⟨k, hk, hka⟩
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hka ht)).trans
      (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  have htotal : (∫ ω, f m ω ∂μ) ≤
      Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) := by
    have h := (HasSubgaussianMGF.sum_of_iIndepFun hind
      (s := Finset.range (m + 1)) (fun i _ => hmgf i)).mgf_le t
    simpa [f, mgf] using h
  have hbound : Real.exp (t * a) *
      μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) := by
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (Real.exp_pos _).le).trans
      (hr'.trans ((setIntegral_le_integral (hs.integrable m)
        (ae_of_all _ (fun _ => (Real.exp_pos _).le))).trans htotal))
  calc
    _ ≤ Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) / Real.exp (t * a) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

lemma partial_sum_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  have hc' : 0 < (c : ℝ) := hc
  have hp : 0 < (m + 1 : ℝ) := by positivity
  have h := partial_sum_maximal_exponential hX hind hmgf hmean m
    (a := a) (t := a / ((m + 1) * (c : ℝ))) (by positivity)
  convert h using 1
  congr 1
  field_simp
  ring

lemma partial_sum_abs_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X i ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  have hp := partial_sum_maximal_tail hX hind hmgf hmean hc m ha
  have hn := partial_sum_maximal_tail (X := fun i ω => -X i ω)
    (fun i => (hX i).neg) (hind.comp (fun _ x => -x) (fun _ => measurable_neg))
    (fun i => (hmgf i).neg) (fun i => by rw [integral_neg, hmean, neg_zero]) hc m ha
  let A : Set Ω := {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω}
  let B : Set Ω := {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), -X i ω}
  have hs : {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X i ω|} ⊆ A ∪ B := by
    rintro ω ⟨k, hk, hka⟩
    rcases le_abs.mp hka with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, by simpa only [Finset.sum_neg_distrib] using h⟩
  have h := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le A B)
  change μ.real _ ≤ μ.real A + μ.real B at h
  change μ.real A ≤ _ at hp
  change μ.real B ≤ _ at hn
  linarith

lemma block_prefix_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (start m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X (start + i) ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  exact partial_sum_abs_maximal_tail (fun i => hX (start + i))
    (hind.precomp (fun i j h => Nat.add_left_cancel h))
    (fun i => hmgf (start + i)) (fun i => hmean (start + i)) hc m ha

noncomputable def blockThreshold (c : ℝ≥0) (m j r : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt (2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16))

lemma blockThreshold_sq (c : ℝ≥0) (m j r : ℕ) (h : ℝ) :
    blockThreshold c m j r h ^ 2 =
      2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16) := by
  apply Real.sq_sqrt
  positivity

lemma block_prefix_dyadic_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (start m j r : ℕ) (h : ℝ) :
    μ.real {ω | ∃ k ≤ m, blockThreshold c m j r h ≤
      |∑ i ∈ Finset.range (k + 1), X (start + i) ω|} ≤
      2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r) := by
  have ht := block_prefix_tail hX hind hmgf hmean hc start m
    (a := blockThreshold c m j r h) (Real.sqrt_nonneg _)
  rw [blockThreshold_sq] at ht
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have he : -(2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16)) /
      (2 * (m + 1) * (c : ℝ)) = -h ^ 2 + (j + r : ℕ) * (-Real.log 16) := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_neg (Real.log 16), Real.exp_log (by norm_num : (0 : ℝ) < 16)] at ht
  simpa only [one_div, mul_assoc] using ht

lemma geometric_half_sum_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).sum_le_tsum
    (Finset.range N) (fun _ _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)] at h
  norm_num at h ⊢
  exact h

omit [IsProbabilityMeasure μ] in
lemma finite_scale_shell_union_bound (A : ℕ → ℕ → ℕ → Set Ω)
    (B : ℕ → ℕ → Finset ℕ) (J R : ℕ) {C h : ℝ} (hC : 0 ≤ C)
    (hcard : ∀ j r, ((B j r).card : ℝ) ≤ C * (8 : ℝ) ^ (j + r))
    (hprob : ∀ j r b, b ∈ B j r → μ.real (A j r b) ≤
      2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) :
    μ.real (⋃ j ∈ Finset.range J, ⋃ r ∈ Finset.range R, ⋃ b ∈ B j r, A j r b) ≤
      8 * C * Real.exp (-h ^ 2) := by
  have hbr (j r : ℕ) : μ.real (⋃ b ∈ B j r, A j r b) ≤
      2 * C * Real.exp (-h ^ 2) * (1 / 2 : ℝ) ^ (j + r) := by
    calc
      _ ≤ ∑ b ∈ B j r, μ.real (A j r b) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ B j r, 2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r) :=
        Finset.sum_le_sum (fun b hb => hprob j r b hb)
      _ = (B j r).card * (2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) := by simp
      _ ≤ (C * (8 : ℝ) ^ (j + r)) *
          (2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) :=
        mul_le_mul_of_nonneg_right (hcard j r) (by positivity)
      _ = _ := by
        have he : (8 : ℝ) ^ (j + r) * (1 / 16 : ℝ) ^ (j + r) = (1 / 2 : ℝ) ^ (j + r) := by
          rw [← mul_pow]
          norm_num
        calc
          _ = 2 * C * Real.exp (-h ^ 2) * ((8 : ℝ) ^ (j + r) * (1 / 16 : ℝ) ^ (j + r)) := by ring
          _ = _ := by rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range J, μ.real (⋃ r ∈ Finset.range R, ⋃ b ∈ B j r, A j r b) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range R, μ.real (⋃ b ∈ B j r, A j r b) := by
      exact Finset.sum_le_sum fun _ _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range R,
        2 * C * Real.exp (-h ^ 2) * (1 / 2 : ℝ) ^ (j + r) := by
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun r _ => hbr j r
    _ = 2 * C * Real.exp (-h ^ 2) *
        (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j) *
        (∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r) := by
      simp_rw [pow_add, ← mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
    _ ≤ 2 * C * Real.exp (-h ^ 2) * 2 * 2 := by
      gcongr
      · exact geometric_half_sum_le_two J
      · exact geometric_half_sum_le_two R
    _ = _ := by ring

def blockShell (j : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range (2 * 8 ^ j)
  | r + 1 => Finset.Ico (2 ^ (r + 1) * 8 ^ j) (2 ^ (r + 2) * 8 ^ j)

lemma blockShell_card (j r : ℕ) :
    ((blockShell j r).card : ℝ) ≤ 2 * (8 : ℝ) ^ (j + r) := by
  cases r with
  | zero => simp [blockShell]
  | succ r =>
    have hpow : (2 : ℕ) ^ (r + 1) ≤ 8 ^ (r + 1) := Nat.pow_le_pow_left (by decide) _
    have he : 2 ^ (r + 2) * 8 ^ j - 2 ^ (r + 1) * 8 ^ j = 2 ^ (r + 1) * 8 ^ j := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      have hid : 2 ^ (r + 1) * 2 * 8 ^ j = 2 * (2 ^ (r + 1) * 8 ^ j) := by ring
      rw [hid]
      omega
    rw [blockShell, Nat.card_Ico, he]
    push_cast
    rw [pow_add (8 : ℝ) j (r + 1)]
    have hp : (2 : ℝ) ^ (r + 1) ≤ 8 ^ (r + 1) := by exact_mod_cast hpow
    calc
      _ ≤ 8 ^ (r + 1) * (8 : ℝ) ^ j := mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ _ := by nlinarith [show 0 ≤ (8 : ℝ) ^ j * 8 ^ (r + 1) by positivity]

lemma blockShell_covers (j b : ℕ) :
    ∃ r ≤ b, b ∈ blockShell j r := by
  by_cases hb : b < 2 * 8 ^ j
  · exact ⟨0, Nat.zero_le _, by simpa [blockShell]⟩
  · have h8 : 0 < (8 : ℕ) ^ j := by positivity
    have hq : 2 ≤ b / 8 ^ j := (Nat.le_div_iff_mul_le h8).mpr (Nat.le_of_not_gt hb)
    let r := Nat.log 2 (b / 8 ^ j)
    have hr : 0 < r := Nat.log_pos (by decide) hq
    have hlo : 2 ^ r * 8 ^ j ≤ b :=
      (Nat.le_div_iff_mul_le h8).mp (Nat.pow_log_le_self 2 (by omega : b / 8 ^ j ≠ 0))
    have hhi : b < 2 ^ (r + 1) * 8 ^ j :=
      (Nat.div_lt_iff_lt_mul h8).mp (Nat.lt_pow_succ_log_self (by decide) _)
    refine ⟨r, (Nat.log_le_self _ _).trans (Nat.div_le_self _ _), ?_⟩
    obtain ⟨r', heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [heq] at hlo hhi ⊢
    simpa [blockShell, Nat.succ_eq_add_one, Nat.add_assoc] using And.intro hlo hhi

lemma blockShell_lower (j r b : ℕ) (hr : 0 < r) (hb : b ∈ blockShell j r) :
    2 ^ r * 8 ^ j ≤ b := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact (Finset.mem_Ico.mp hb).1

def multiscaleBad (X : ℕ → Ω → ℝ) (c : ℝ≥0) (d : ℕ → ℕ)
    (J N : ℕ) (h : ℝ) : Set Ω :=
  ⋃ j ∈ Finset.range J, ⋃ r ∈ Finset.range (N + 1), ⋃ b ∈ blockShell j r,
    {ω | ∃ k ≤ d j, blockThreshold c (d j) j r h ≤
      |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω|}

lemma multiscaleBad_measurable (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (c : ℝ≥0) (d : ℕ → ℕ) (J N : ℕ) (h : ℝ) :
    MeasurableSet (multiscaleBad X c d J N h) := by
  unfold multiscaleBad
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro _
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro k
  exact (MeasurableSet.const _).inter
    (measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => hX _)).abs)

lemma multiscaleBad_probability {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (d : ℕ → ℕ) (J N : ℕ) (h : ℝ) :
    μ.real (multiscaleBad X c d J N h) ≤ 16 * Real.exp (-h ^ 2) := by
  simpa only [multiscaleBad, show (8 : ℝ) * 2 = 16 by norm_num] using
    finite_scale_shell_union_bound
      (fun j r b => {ω | ∃ k ≤ d j, blockThreshold c (d j) j r h ≤
        |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω|})
      blockShell J (N + 1) (by norm_num : (0 : ℝ) ≤ 2)
      blockShell_card (fun j r b _ => block_prefix_dyadic_tail hX hind hmgf hmean hc _ _ _ _ _)

omit [MeasurableSpace Ω] in
lemma good_multiscale_prefix {X : ℕ → Ω → ℝ} {c : ℝ≥0} {d : ℕ → ℕ}
    {J N : ℕ} {h : ℝ} {ω : Ω} (hω : ω ∉ multiscaleBad X c d J N h)
    {j b : ℕ} (hj : j < J) (hb : b ≤ N) :
    ∃ r ≤ b, b ∈ blockShell j r ∧ ∀ k ≤ d j,
      |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω| ≤
        blockThreshold c (d j) j r h := by
  obtain ⟨r, hr, hbr⟩ := blockShell_covers j b
  refine ⟨r, hr, hbr, fun k hk => le_of_lt ?_⟩
  by_contra! hbad
  apply hω
  simp only [multiscaleBad, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨j, Finset.mem_range.mpr hj, r, Finset.mem_range.mpr (by omega), b, hbr, k, hk, hbad⟩

omit [MeasurableSpace Ω] in
lemma good_multiscale_prefix_all {X : ℕ → Ω → ℝ} {c : ℝ≥0} {d : ℕ → ℕ}
    {J N : ℕ} {h : ℝ} {ω : Ω} (hω : ω ∉ multiscaleBad X c d J N h)
    {j r b : ℕ} (hj : j < J) (hr : r ≤ N) (hb : b ∈ blockShell j r) {k : ℕ} (hk : k ≤ d j) :
    |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω| ≤ blockThreshold c (d j) j r h := by
  apply le_of_lt
  by_contra! hbad
  apply hω
  simp only [multiscaleBad, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨j, Finset.mem_range.mpr hj, r, Finset.mem_range.mpr (by omega), b, hb, k, hk, hbad⟩

end

lemma block_summation_by_parts (ξ w : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, ξ i * w i =
      (∑ i ∈ Finset.range m, ξ i) * w m +
        ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), ξ j) * (w i - w (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring

lemma block_zero_sum_bound (ξ w : ℕ → ℝ) (m : ℕ) {B : ℝ}
    (htotal : ∑ i ∈ Finset.range (m + 1), ξ i = 0)
    (hpref : ∀ k ≤ m, |∑ i ∈ Finset.range (k + 1), ξ i| ≤ B) :
    |∑ i ∈ Finset.range (m + 1), ξ i * w i| ≤
      B * ∑ i ∈ Finset.range m, |w (i + 1) - w i| := by
  rw [block_summation_by_parts, htotal, zero_mul, zero_add,
    Finset.sum_range_succ, htotal, zero_mul, add_zero]
  calc
    _ ≤ ∑ i ∈ Finset.range m,
        |(∑ j ∈ Finset.range (i + 1), ξ j) * (w i - w (i + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, B * |w (i + 1) - w i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_sub_comm (w i)]
      exact mul_le_mul_of_nonneg_right (hpref i (Nat.le_of_lt (Finset.mem_range.mp hi)))
        (abs_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

lemma block_prefix_weight_bound (ξ w : ℕ → ℝ) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpref : ∀ k ≤ m, |∑ i ∈ Finset.range (k + 1), ξ i| ≤ B) :
    |∑ i ∈ Finset.range (m + 1), ξ i * w i| ≤
      B / (m + 1) * (∑ i ∈ Finset.range (m + 1), |w i|) +
        2 * B * ∑ i ∈ Finset.range m, |w (i + 1) - w i| := by
  let avg : ℝ := (∑ i ∈ Finset.range (m + 1), ξ i) / (m + 1)
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have havg : |avg| ≤ B / (m + 1) := by
    dsimp [avg]
    rw [abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right (hpref m le_rfl) hm.le
  have hc (k : ℕ) : (∑ i ∈ Finset.range k, (ξ i - avg)) =
      (∑ i ∈ Finset.range k, ξ i) - k * avg := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hz : ∑ i ∈ Finset.range (m + 1), (ξ i - avg) = 0 := by
    rw [hc]
    dsimp [avg]
    push_cast
    field_simp
    ring
  have hp (k : ℕ) (hk : k ≤ m) : |∑ i ∈ Finset.range (k + 1), (ξ i - avg)| ≤ 2 * B := by
    rw [hc]
    have hk' : (k + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ hk
    have hpart : |(k + 1 : ℝ) * avg| ≤ B := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
      calc
        _ ≤ (k + 1) * (B / (m + 1)) := mul_le_mul_of_nonneg_left havg (by positivity)
        _ ≤ (m + 1) * (B / (m + 1)) := mul_le_mul_of_nonneg_right hk' (by positivity)
        _ = B := by field_simp
    have ha := abs_sub (∑ i ∈ Finset.range (k + 1), ξ i) ((k + 1 : ℝ) * avg)
    push_cast
    exact ha.trans (by linarith [hpref k hk])
  have hs := block_zero_sum_bound (fun i => ξ i - avg) w m hz hp
  have hid : (∑ i ∈ Finset.range (m + 1), ξ i * w i) =
      avg * (∑ i ∈ Finset.range (m + 1), w i) +
        (∑ i ∈ Finset.range (m + 1), (ξ i - avg) * w i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add ?_ hs)
  rw [abs_mul]
  exact mul_le_mul havg (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by positivity)

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

end CriticalSK

end

end OAI
