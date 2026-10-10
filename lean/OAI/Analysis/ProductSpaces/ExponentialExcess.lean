import OAI.Analysis.ProductSpaces.ExponentialMixture

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section ExponentialExcess
variable {ι : Type uι} [Fintype ι]

lemma exponential_eval_memLp (i : ι) : MemLp (fun u : ι → ℝ => u i) 2 exponentialVector :=
  exponentialLaw_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ => exponentialLaw) i)

lemma exponential_positive_eval_memLp (i : ι) : MemLp (fun u : ι → ℝ => max (u i) 0) 2 exponentialVector := by
  apply MemLp.ae_eq (f := fun u : ι → ℝ => u i) ?_ (exponential_eval_memLp i)
  filter_upwards [exponentialVector_positive (ι := ι)] with u hu
  exact (max_eq_left (hu i).le).symm

lemma exponential_positive_eval_mean (i : ι) :
    (∫ u : ι → ℝ, max (u i) 0 ∂exponentialVector) = 1 := by
  calc
    _ = ∫ u : ι → ℝ, u i ∂exponentialVector := by
      apply integral_congr_ae
      filter_upwards [exponentialVector_positive (ι := ι)] with u hu
      exact max_eq_left (hu i).le
    _ = 1 := (exponential_eval_hasLaw i).integral_comp (by fun_prop) |>.trans exponentialLaw_mean

lemma exponential_positive_eval_second (i : ι) :
    (∫ u : ι → ℝ, (max (u i) 0) ^ 2 ∂exponentialVector) = 2 := by
  calc
    _ = ∫ u : ι → ℝ, (u i) ^ 2 ∂exponentialVector := by
      apply integral_congr_ae
      filter_upwards [exponentialVector_positive (ι := ι)] with u hu
      rw [max_eq_left (hu i).le]
    _ = 2 := (exponential_eval_hasLaw i).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop) |>.trans exponentialLaw_second

lemma exponentialVariance_tail (a : ι → ℝ) (ha : 0 < ∑ i, a i ^ 2) :
    1 / 8 ≤ (exponentialVector (ι := ι)).real {u | (∑ i, a i ^ 2) ≤ exponentialVariance a u} := by
  have h := weighted_sum_tail a (fun i (u : ι → ℝ) => max (u i) 0)
    exponential_positive_eval_memLp (fun _ => by fun_prop) (fun _ _ => le_max_right _ _)
    exponential_positive_eval_mean 2 (by norm_num)
    (fun i => (exponential_positive_eval_second i).le) ha
  have he : {u : ι → ℝ | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * max (u i) 0} =
      {u : ι → ℝ | (∑ i, a i ^ 2) ≤ exponentialVariance a u} := by
    ext u
    simp only [Set.mem_ofPred_eq, exponentialVariance]
    constructor <;> intro hh <;> linarith
  norm_num only [show (4 * (2 : ℝ)) = 8 by norm_num] at h
  rwa [he] at h

lemma integrable_exponentialVariance (a : ι → ℝ) : Integrable (exponentialVariance a) exponentialVector :=
  ((weighted_sum_memLp_two a (fun i (u : ι → ℝ) => max (u i) 0)
    exponential_positive_eval_memLp).integrable (by norm_num)).const_mul 2

lemma integrable_exponentialMixture (a : ι → ℝ) :
    Integrable (exponentialMixture a) (exponentialVector.prod (gaussianReal 0 1)) := by
  have hs : Integrable (fun u => Real.sqrt (exponentialVariance a u)) exponentialVector := by
    apply ((integrable_exponentialVariance a).add (integrable_const 1)).mono'
      (measurable_exponentialVariance a).sqrt.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (exponentialVariance a u) ≤ exponentialVariance a u + 1
    have hv := exponentialVariance_nonneg a u
    have hsq := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg (exponentialVariance a u)
    nlinarith [sq_nonneg (Real.sqrt (exponentialVariance a u) - 1)]
  exact hs.mul_prod ((memLp_id_gaussianReal 1).integrable (by norm_num))

lemma excess_scaled_lower (K s v x : ℝ) (hs : 0 ≤ s) (hsv : s ≤ v) :
    s * max (|x| - 2 * K) 0 ≤ excess 1 (2 * K * s) (v * x) := by
  unfold excess
  rw [abs_mul, abs_of_nonneg (hs.trans hsv), one_mul, mul_max_of_nonneg _ _ hs, mul_zero]
  apply max_le_max_right
  have h := mul_le_mul_of_nonneg_right hsv (abs_nonneg x)
  nlinarith

lemma exponential_mixture_excess (a : ι → ℝ) (K : ℝ) :
    (1 / 8 : ℝ) * Real.sqrt (∑ i, a i ^ 2) *
      (∫ g : ℝ, max (|g| - 2 * K) 0 ∂gaussianReal 0 1) ≤
      ∫ z : (ι → ℝ) × ℝ, excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2))
        (exponentialMixture a z) ∂exponentialVector.prod (gaussianReal 0 1) := by
  let S := ∑ i, a i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hS0 : S = 0
  · change (1 / 8 : ℝ) * Real.sqrt S * _ ≤ _
    rw [hS0, Real.sqrt_zero, mul_zero, zero_mul]
    exact integral_nonneg (fun _ => excess_nonneg _ _ _)
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  let A : Set (ι → ℝ) := {u | S ≤ exponentialVariance a u}
  have hAm : MeasurableSet A := measurableSet_le measurable_const (measurable_exponentialVariance a)
  let c := Real.sqrt S * (∫ g : ℝ, max (|g| - 2 * K) 0 ∂gaussianReal 0 1)
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun _ => le_max_right _ _)
  have hint := integrable_excess (integrable_exponentialMixture a) 1 (2 * K * Real.sqrt S)
  rw [integral_prod _ hint]
  calc
    _ = (1 / 8 : ℝ) * c := by dsimp [c, S]; ring
    _ ≤ exponentialVector.real A * c :=
      mul_le_mul_of_nonneg_right (exponentialVariance_tail a hSp) hc
    _ = ∫ u : ι → ℝ, A.indicator (fun _ => c) u ∂exponentialVector := by
      simp [integral_indicator hAm, mul_comm]
    _ ≤ ∫ u : ι → ℝ, ∫ g : ℝ, excess 1 (2 * K * Real.sqrt S)
        (exponentialMixture a (u, g)) ∂gaussianReal 0 1 ∂exponentialVector := by
      apply integral_mono ((integrable_const _).indicator hAm) hint.integral_prod_left
      intro u
      by_cases hu : u ∈ A
      · rw [Set.indicator_of_mem hu]
        change Real.sqrt S * (∫ g, max (|g| - 2 * K) 0 ∂gaussianReal 0 1) ≤ _
        rw [← integral_const_mul]
        simp only [exponentialMixture]
        apply integral_mono ((integrable_gaussian_abs_excess K).const_mul _)
          (integrable_excess (((memLp_id_gaussianReal 1).integrable (by norm_num)).const_mul _) _ _)
        intro g
        exact excess_scaled_lower K (Real.sqrt S) (Real.sqrt (exponentialVariance a u)) g
          (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hu)
      · rw [Set.indicator_of_notMem hu]
        exact integral_nonneg fun _ => excess_nonneg _ _ _

lemma integrable_exponential_linear (a : ι → ℝ) (b : ℝ) :
    Integrable (fun u : ι → ℝ => b + ∑ i, a i * u i) exponentialVector := by
  apply (integrable_const b).add
  exact integrable_finsetSum _ (fun i _ => ((exponential_eval_memLp i).integrable (by norm_num)).const_mul _)

lemma exponential_scalar_excess_unit (a : ι → ℝ) (b K : ℝ) :
    excessConstant K * Real.sqrt (∑ i, a i ^ 2) ≤
      ∫ u : ι → ℝ, excess 1 (K * Real.sqrt (∑ i, a i ^ 2)) (b + ∑ i, a i * u i) ∂exponentialVector := by
  have hcopy := integral_excess_independent_copy (integrable_exponential_linear a b)
    (by norm_num : (0 : ℝ) ≤ 1) (K * Real.sqrt (∑ i, a i ^ 2))
  have hd : ∀ z : (ι → ℝ) × (ι → ℝ),
      excess 1 (K * Real.sqrt (∑ i, a i ^ 2))
      (((b + ∑ i, a i * z.1 i) - (b + ∑ i, a i * z.2 i)) / 2) =
      excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2)) (exponentialDifference a z) / 2 := by
    intro z
    have he : (b + ∑ i, a i * z.1 i) - (b + ∑ i, a i * z.2 i) = exponentialDifference a z := by
      simp only [exponentialDifference, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he]
    unfold excess
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul, one_mul,
      ← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  simp_rw [hd] at hcopy
  rw [integral_div] at hcopy
  have hm : (∫ z : (ι → ℝ) × (ι → ℝ),
      excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2)) (exponentialDifference a z)
      ∂exponentialVector.prod exponentialVector) =
      ∫ z : (ι → ℝ) × ℝ, excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2))
        (exponentialMixture a z) ∂exponentialVector.prod (gaussianReal 0 1) := by
    have h := exponential_difference_mixture a
    have hm : Measurable (exponentialDifference a) := by unfold exponentialDifference; fun_prop
    rw [← integral_map hm.aemeasurable (by unfold excess; fun_prop), h,
      integral_map (measurable_exponentialMixture a).aemeasurable (by unfold excess; fun_prop)]
  rw [hm] at hcopy
  have hlow := exponential_mixture_excess a K
  unfold excessConstant
  nlinarith

end ExponentialExcess
end IndependentProducts

namespace IndependentProducts

lemma excess_threshold_scale (t K s r x : ℝ) (ht : 0 ≤ t) (hr : r ≤ t * K * s) :
    t * excess 1 (K * s) x ≤ excess t r x := by
  unfold excess
  rw [one_mul, mul_max_of_nonneg _ _ ht, mul_zero]
  apply max_le_max_right
  nlinarith

lemma exponential_scalar_excess {ι : Type uι} [Fintype ι] (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 < K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (t * excessConstant K) * Real.sqrt (∑ i, a i ^ 2) - (excessConstant K / K) * r ≤
      ∫ u : ι → ℝ, excess t r (b + ∑ i, a i * u i) ∂exponentialVector := by
  let s := Real.sqrt (∑ i, a i ^ 2)
  have hc : 0 ≤ excessConstant K := (excessConstant_pos K).le
  by_cases hgood : r ≤ t * K * s
  · calc
      _ ≤ t * (excessConstant K * s) := by
        have hh := mul_nonneg (div_nonneg hc hK.le) hr
        dsimp [s]
        nlinarith
      _ ≤ t * (∫ u : ι → ℝ, excess 1 (K * s) (b + ∑ i, a i * u i) ∂exponentialVector) :=
        mul_le_mul_of_nonneg_left (exponential_scalar_excess_unit a b K) ht
      _ = ∫ u : ι → ℝ, t * excess 1 (K * s) (b + ∑ i, a i * u i) ∂exponentialVector :=
        (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono
        ((integrable_excess (integrable_exponential_linear a b) 1 (K * s)).const_mul t)
        (integrable_excess (integrable_exponential_linear a b) t r)
        (fun u => excess_threshold_scale t K s r (b + ∑ i, a i * u i) ht hgood)
  · have hbad : t * K * s ≤ r := (lt_of_not_ge hgood).le
    have hd : t * s ≤ r / K := (le_div_iff₀ hK).mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hd hc
    have hn : (t * excessConstant K) * s - (excessConstant K / K) * r ≤ 0 := by
      calc
        _ = excessConstant K * (t * s) - excessConstant K * (r / K) := by ring
        _ ≤ 0 := sub_nonpos.mpr hh
    exact hn.trans (integral_nonneg (fun _ => excess_nonneg _ _ _))

end IndependentProducts

end

end OAI
