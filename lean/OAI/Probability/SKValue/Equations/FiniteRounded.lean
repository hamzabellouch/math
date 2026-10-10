import Mathlib
import OAI.Probability.SKValue.Equations.MemLpLinearCombination
import OAI.Probability.SKValue.Gaussian.CoordinateDependsBefore

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

noncomputable def finiteRounded {N : ℕ} (U : (Fin (N+1) → ℝ) → ℝ) :
    (Fin (N+1) → ℝ) → ℝ :=
  fun z ↦ Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)

noncomputable def finiteRawMartingale {N : ℕ} (δ : ℝ)
    (H : Fin N → (Fin (N+1) → ℝ) → ℝ) : (Fin (N+1) → ℝ) → ℝ :=
  fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z

lemma finiteRawMartingale_eq_normalized {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) :
    finiteRawMartingale δ H = fun z ↦ ∑ i : Fin N,
      (Real.sqrt δ / predictableNormalizer (H i) (gaussianProduct (Fin (N+1)))) *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z := by
  ext z
  apply Finset.sum_congr rfl
  intro i _
  have hc := ne_of_gt (predictableNormalizer_pos (hpos i))
  simp only [normalizedIncrement]
  field_simp

lemma finiteRawMartingale_memLp {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  rw [finiteRawMartingale_eq_normalized hpos]
  exact memLp_linearCombination (fun i ↦ normalizedIncrement_memLp_two (hH i)
    (coordinate_hasLaw N i) ((hp i).independent (by omega) (hm i))) _

lemma finiteRawMartingale_normalized_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z *
      normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ / predictableNormalizer (H j) (gaussianProduct (Fin (N+1))) := by
  rw [finiteRawMartingale_eq_normalized hpos]
  exact orthogonal_linearCombination_coefficient
    (fun i ↦ normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i))) (normalized_family_orthonormal hm hp hpos) _ j

lemma finiteRawMartingale_coordinate_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ * ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  rw [finiteRawMartingale_eq_normalized hpos,
    integral_linearCombination_mul
      (fun i ↦ normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i)
        ((hp i).independent (by omega) (hm i)))
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))]
  simp_rw [normalized_coordinate_pair hm hp]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hc := ne_of_gt (predictableNormalizer_pos (hpos j))
  field_simp

lemma finite_coefficient_L2_errors {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1)))
    (hUm : Measurable U) (hUp : DependsBefore N U) (hUb : ∀ z, |U z|≤1) :
    (∑ i : Fin N, ((∫ z, finiteRounded U z *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1))) -
      Real.sqrt δ / predictableNormalizer (H i) (gaussianProduct (Fin (N+1))))^2) ≤
      ∫ z, (U z-finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1)) ∧
    (∑ i : Fin N, ((∫ z, finiteRounded U z * coordinate N i z ∂gaussianProduct (Fin (N+1))) -
      Real.sqrt δ * ∫ z, H i z ∂gaussianProduct (Fin (N+1)))^2) ≤
      ∫ z, (U z-finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1)) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  have hU : MemLp U 2 (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hUm.aestronglyMeasurable 1 (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hUb))
  have hg : ∀ i, MemLp (normalizedIncrement (H i) (coordinate N i)
      (gaussianProduct (Fin (N+1)))) 2 (gaussianProduct (Fin (N+1))) := fun i ↦
    normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i) ((hp i).independent (by omega) (hm i))
  have hM := finiteRawMartingale_memLp (δ := δ) hm hp hH hpos
  have hA : ∀ i : Fin N, (∫ z, finiteRounded U z *
      normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1))) =
      ∫ z, U z * normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1)) := fun i ↦
    finite_rounding_coefficient hUm (measurable_normalizedIncrement (hm i))
      ((hg i).integrable (by norm_num)) hUb hUp
      ((normalizedIncrement_dependsBefore (by omega) (hp i)).mono (by omega))
  have hB : ∀ i : Fin N, (∫ z, finiteRounded U z * coordinate N i z
      ∂gaussianProduct (Fin (N+1))) = ∫ z, U z * coordinate N i z
        ∂gaussianProduct (Fin (N+1)) := fun i ↦
    finite_rounding_coefficient hUm (measurable_coordinate N i)
      ((gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num)).integrable (by norm_num)) hUb hUp
      (coordinate_dependsBefore (by omega) i.isLt)
  constructor
  · have h := finite_projection_error hg (normalized_family_orthonormal hm hp hpos) hU hM
    simpa only [finiteRawMartingale_normalized_coefficient hm hp hH hpos, hA] using h
  · have h := finite_projection_error
      (fun i : Fin N ↦ gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num))
      (coordinate_family_orthonormal N) hU hM
    simpa only [finiteRawMartingale_coordinate_coefficient hm hp hH hpos, hB] using h

lemma finiteRounded_measurable {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) : Measurable (finiteRounded U) := by
  apply measurable_real_sign.comp
  exact (hU.add ((((monotone_cdf standardGaussian).measurable).comp
    (measurable_coordinate N N)).const_mul 2)).sub_const 1

lemma finiteRounded_memLp {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) : MemLp (finiteRounded U) 2 (gaussianProduct (Fin (N+1))) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  exact MemLp.of_bound (finiteRounded_measurable hU).aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs, finiteRounded] using abs_real_sign_le_one
        (U z+2*cdf standardGaussian (coordinate N N z)-1)))

lemma finiteRounded_square_le_one {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) :
    (∫ z, (finiteRounded U z)^2 ∂gaussianProduct (Fin (N+1))) ≤ 1 := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  calc
    _ ≤ ∫ _ : Fin (N+1) → ℝ, (1 : ℝ) ∂gaussianProduct (Fin (N+1)) := by
      apply integral_mono (finiteRounded_memLp hU).integrable_sq (integrable_const 1)
      intro z
      exact (sq_le_one_iff_abs_le_one _).2 (abs_real_sign_le_one _)
    _ = _ := by simp

lemma finiteRounded_coordinate_norms {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) :
    (∑ i : Fin N, (∫ z, finiteRounded U z * coordinate N i z
      ∂gaussianProduct (Fin (N+1)))^2) ≤ 1 ∧
    |∫ z, finiteRounded U z * coordinate N N z ∂gaussianProduct (Fin (N+1))| ≤ 1 := by
  have hF := finiteRounded_memLp hU
  constructor
  · exact (finite_bessel (fun i : Fin N ↦ gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num))
      (coordinate_family_orthonormal N) hF).trans (finiteRounded_square_le_one hU)
  · have h := finite_bessel (g := fun _ : Unit ↦ coordinate N N)
      (fun _ ↦ gaussian_memLp (coordinate_hasLaw N N) 2 (by norm_num))
      (fun _ _ ↦ by simpa only [← pow_two, ite_true] using gaussian_second_moment (coordinate_hasLaw N N)) hF
    simp only [Fintype.sum_unique] at h
    exact (sq_le_one_iff_abs_le_one _).mp (h.trans (finiteRounded_square_le_one hU))

lemma sqrt_div_normalizer_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H : Ω → ℝ} {δ : ℝ} (hδ : 0≤δ) :
    (Real.sqrt δ / predictableNormalizer H μ)^2 = δ * ∫ z, (H z)^2 ∂μ := by
  simp only [predictableNormalizer, div_inv_eq_mul, mul_pow, Real.sq_sqrt hδ,
    Real.sq_sqrt (integral_nonneg (fun z ↦ sq_nonneg (H z)))]

lemma sqrt_div_normalizer_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {H : Ω → ℝ} {δ K : ℝ}
    (hH : MemLp H 2 μ) (hK : 0≤K) (hbound : ∀ᵐ z ∂μ, |H z|≤K) :
    |Real.sqrt δ / predictableNormalizer H μ| ≤ Real.sqrt δ * K := by
  have hi : (∫ z, (H z)^2 ∂μ)≤K^2 := by
    calc
      _ ≤ ∫ _ : Ω, K^2 ∂μ := by
        apply integral_mono_ae hH.integrable_sq (integrable_const _)
        filter_upwards [hbound] with z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hz
      _ = _ := by simp
  simp only [predictableNormalizer, div_inv_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.sqrt_sq hK] using Real.sqrt_le_sqrt hi)
    (Real.sqrt_nonneg δ)

end SKValue

open Filter Set
open scoped Topology BigOperators

end

end OAI
