import OAI.Analysis.PlanarEndpoint.AlmostOrthogonal
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate BigOperators
namespace PlanarEndpoint

def spatialDecay (N : ℝ) (z : Plane) : ℝ := N^2/(1+N*‖z‖)^4

lemma spatialDecay_nonneg {N : ℝ} (z : Plane) : 0 ≤ spatialDecay N z := by
  unfold spatialDecay
  positivity

lemma spatialDecay_le {N : ℝ} (hN : 0 ≤ N) (z : Plane) : spatialDecay N z ≤ N^2 := by
  have h : 1 ≤ 1+N*‖z‖ := by linarith [mul_nonneg hN (norm_nonneg z)]
  have h4 : 1 ≤ (1+N*‖z‖)^4 := one_le_pow₀ h
  unfold spatialDecay
  exact div_le_self (sq_nonneg _) h4

lemma spatialDecay_one_integrable : Integrable (spatialDecay 1) volume := by
  have h := (integrable_one_add_norm (μ := (volume : Measure Plane))
    (show (Module.finrank ℝ Plane : ℝ) < (4 : ℝ) by norm_num))
  convert h using 1
  funext z
  simp [spatialDecay]

lemma spatialDecay_scale {N : ℝ} (hN : 0 ≤ N) (z : Plane) :
    spatialDecay N z = N^2 * spatialDecay 1 (N • z) := by
  simp [spatialDecay, norm_smul, Real.norm_eq_abs, abs_of_nonneg hN, div_eq_mul_inv]

lemma spatialDecay_integrable {N : ℝ} (hN : 0 < N) : Integrable (spatialDecay N) volume := by
  convert (spatialDecay_one_integrable.comp_smul hN.ne').const_mul (N^2) using 1
  funext z
  exact spatialDecay_scale hN.le z

lemma integral_spatialDecay {N : ℝ} (hN : 0 < N) :
    (∫ z, spatialDecay N z) = ∫ z, spatialDecay 1 z := by
  simp_rw [spatialDecay_scale hN.le]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume _ N (hR := hN.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hN.ne'), one_mul]

lemma integrable_spatialDecay_prod (μ : Measure Plane) [IsFiniteMeasure μ]
    {N : ℝ} (hN : 0 < N) :
    Integrable (fun z : Plane × Plane => spatialDecay N (z.1-z.2)) (μ.prod volume) := by
  have hm : AEStronglyMeasurable (fun z : Plane × Plane => spatialDecay N (z.1-z.2))
      (μ.prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold spatialDecay
    fun_prop
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards [] with x
    exact (spatialDecay_integrable hN).comp_sub_left x
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (spatialDecay_nonneg _),
      integral_sub_left_eq_self]
    exact integrable_const _

lemma spatialDecay_schur (μ : Measure Plane) [IsFiniteMeasure μ]
    (hμ : μ ≤ volume) {N : ℝ} (hN : 0 < N) :
    (∫ z : Plane × Plane, spatialDecay N (z.1-z.2) ∂μ.prod μ) ≤
      (∫ z, spatialDecay 1 z) * μ.real univ := by
  apply le_trans (integral_mono_measure (Measure.prod_mono le_rfl hμ)
    (ae_of_all _ (fun z => spatialDecay_nonneg _)) (integrable_spatialDecay_prod μ hN))
  rw [integral_prod (f := fun z : Plane × Plane => spatialDecay N (z.1-z.2))
    (integrable_spatialDecay_prod μ hN)]
  simp_rw [integral_sub_left_eq_self, integral_spatialDecay hN]
  simp [mul_comm]

lemma norm_graphDual_pairing_le_integral (χ : Plane → ℂ) (hχm : Measurable χ)
    (hχ : MemLp χ 2 volume) (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {H : Plane × Plane → ℝ} (hH : Integrable H (μ.prod ν))
    (hK : ∀ᵐ z : Plane × Plane ∂μ.prod ν,
      ‖frequencyKernel χ (z.1-z.2) (T z.1-T z.2)‖ ≤ H z) :
    ‖∫ ξ, graphDual χ μ T w ξ * conj (graphDual χ ν T w ξ)‖ ≤
      ∫ z, H z ∂μ.prod ν := by
  rw [graphDual_pairing χ hχm hχ μ ν hT hw hb]
  apply norm_integral_le_of_norm_le hH
  filter_upwards [hK] with z hz
  simp only [norm_mul, Complex.norm_conj]
  have hww : ‖w z.1‖ * ‖w z.2‖ ≤ 1 := by
    nlinarith [hb z.1, hb z.2, norm_nonneg (w z.1), norm_nonneg (w z.2)]
  exact (mul_le_mul_of_nonneg_right hww (norm_nonneg _)).trans (by simpa using hz)

lemma finite_sum_prod_integral {ι : Type*} [Fintype ι]
    (μ : ι → Measure Plane) [∀ i, IsFiniteMeasure (μ i)]
    {H : Plane × Plane → ℝ} (hH : Integrable H ((∑ i, μ i).prod (∑ i, μ i))) :
    (∑ i, ∑ j, ∫ z, H z ∂(μ j).prod (μ i)) =
      ∫ z, H z ∂(∑ i, μ i).prod (∑ i, μ i) := by
  have he : (∑ i, μ i).prod (∑ i, μ i) = ∑ p : ι × ι, (μ p.1).prod (μ p.2) := by
    rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.prod_sum, Measure.sum_fintype]
  have hi (p : ι × ι) : Integrable H ((μ p.1).prod (μ p.2)) := hH.mono_measure
    (Measure.prod_mono (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ _))
      (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ _)))
  rw [he, integral_finsetSum_measure (fun p _ => hi p), Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma graphPartition_near_far {ι : Type*} [Fintype ι]
    (χ : Plane → ℂ) (hχm : Measurable χ) (hχ : MemLp χ 2 volume)
    (μ : ι → Measure Plane) [∀ i, IsFiniteMeasure (μ i)]
    (hμ : (∑ i, μ i) ≤ volume) (T : Plane → ℝ) (w : Plane → ℂ)
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1)
    (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ ⦃first second⦄, R first second → R second first)
    {D C N : ℝ} (hC : 0 ≤ C) (hN : 0 < N)
    (hdegree : ∀ i, ((Finset.univ.filter (R i)).card : ℝ) ≤ D)
    (hfar : ∀ i j, ¬R i j → ∀ᵐ z : Plane × Plane ∂(μ j).prod (μ i),
      ‖frequencyKernel χ (z.1-z.2) (T z.1-T z.2)‖ ≤ C*spatialDecay N (z.1-z.2)) :
    ‖graphLp χ hχ (∑ i, μ i) T w hT hw hb‖^2 ≤
      D * (∑ i, ‖graphLp χ hχ (μ i) T w hT hw hb‖^2) +
        C * (∫ z, spatialDecay 1 z) * (∑ i, μ i).real univ := by
  let M := ∑ i, μ i
  have hh : Integrable (fun z : Plane × Plane => C*spatialDecay N (z.1-z.2)) (M.prod M) :=
    ((integrable_spatialDecay_prod M hN).mono_measure (Measure.prod_mono le_rfl hμ)).const_mul C
  have hi (i j : ι) : Integrable (fun z : Plane × Plane => C*spatialDecay N (z.1-z.2))
      ((μ j).prod (μ i)) := hh.mono_measure
    (Measure.prod_mono (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ _))
      (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ _)))
  have hA (i j : ι) : 0 ≤ ∫ z : Plane × Plane, C*spatialDecay N (z.1-z.2) ∂(μ j).prod (μ i) :=
    integral_nonneg (fun z => mul_nonneg hC (spatialDecay_nonneg _))
  have hk (i j : ι) (hij : ¬R i j) := norm_graphDual_pairing_le_integral χ hχm hχ
    (μ j) (μ i) hT hw hb (hi i j) (hfar i j hij)
  simp_rw [← inner_graphLp χ hχ _ _ T w hT hw hb] at hk
  have hh' := norm_sum_sq_le_near_error (fun i => graphLp χ hχ (μ i) T w hT hw hb)
    R hR _ hA hdegree hk
  rw [← graphLp_finsetSum_measure Finset.univ χ hχ μ T w hT hw hb] at hh'
  rw [finite_sum_prod_integral μ hh, integral_const_mul] at hh'
  apply hh'.trans
  apply add_le_add le_rfl
  simpa only [M, mul_assoc] using
    mul_le_mul_of_nonneg_left (spatialDecay_schur M hμ hN) hC

end PlanarEndpoint
end

end OAI
