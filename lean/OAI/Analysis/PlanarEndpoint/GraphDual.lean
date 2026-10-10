import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.Oscillation

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
open scoped Topology ComplexConjugate ContDiff
namespace PlanarEndpoint

def graphFourier (μ : Measure Plane) (T : Plane → ℝ) (w : Plane → ℂ) (ξ : Plane) : ℂ :=
  ∫ x, w x * phase x (T x) ξ ∂μ

def graphDual (χ : Plane → ℂ) (μ : Measure Plane) (T : Plane → ℝ) (w : Plane → ℂ) : Plane → ℂ :=
  fun ξ => χ ξ * graphFourier μ T w ξ

lemma measurable_graph_phase {T : Plane → ℝ} (hT : Measurable T) :
    Measurable (fun z : Plane × Plane => phase z.1 (T z.1) z.2) := by
  unfold phase
  fun_prop

lemma integrable_graph_phase (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (ξ : Plane) :
    Integrable (fun x => w x * phase x (T x) ξ) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (hw.mul ((measurable_graph_phase hT).comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [norm_mul, norm_phase, mul_one] using hb x

lemma norm_graphFourier_le (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (ξ : Plane) :
    ‖graphFourier μ T w ξ‖ ≤ μ.real univ := by
  calc
    _ ≤ ∫ x, ‖w x * phase x (T x) ξ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (1 : ℝ) ∂μ := integral_mono (integrable_graph_phase μ hT hw hb ξ).norm
      (integrable_const _) (fun x => by simpa using hb x)
    _ = μ.real univ := by simp

lemma continuous_graphFourier (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) : Continuous (graphFourier μ T w) := by
  apply continuous_iff_continuousAt.2
  intro ξ
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall (fun η => (integrable_graph_phase μ hT hw hb η).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun η => Filter.Eventually.of_forall
      (fun x => by simpa using hb x))
  · exact integrable_const _
  · filter_upwards [] with x
    apply Continuous.continuousAt
    unfold phase
    have hi : Continuous (fun η : Plane => inner ℝ x η) := (innerSL ℝ x).continuous
    fun_prop

lemma graphDual_memLp (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) : MemLp (graphDual χ μ T w) 2 volume := by
  apply (hχ.const_mul (μ.real univ : ℂ)).mono
  · exact ((continuous_graphFourier μ hT hw hb).aestronglyMeasurable.mul
      hχ.aestronglyMeasurable).congr (Filter.Eventually.of_forall (fun ξ => mul_comm _ _))
  · filter_upwards [] with ξ
    have hμ : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    simp only [graphDual, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hμ]
    nlinarith [norm_graphFourier_le μ hT hw hb ξ, norm_nonneg (χ ξ)]

lemma phase_mul_conj (x y ξ : Plane) (t s : ℝ) :
    phase x t ξ * conj (phase y s ξ) = phase (x-y) (t-s) ξ := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

lemma phase_eq_kernel_oscillation (z ξ : Plane) (t : ℝ) :
    phase z t ξ = EndpointKernel.oscillation (EndpointKernel.quadraticPhase (z,t)) 1 ξ := by
  simp only [phase, EndpointKernel.oscillation, EndpointKernel.quadraticPhase, one_mul, mul_comm]

def frequencyKernel (χ : Plane → ℂ) (z : Plane) (t : ℝ) : ℂ :=
  ∫ ξ, χ ξ * conj (χ ξ) * phase z t ξ

lemma integrable_graph_pairing (χ : Plane → ℂ) (hχm : Measurable χ)
    (hχ : MemLp χ 2 volume) (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    Integrable (fun q : Plane × (Plane × Plane) =>
      χ q.1 * conj (χ q.1) * (w q.2.1 * conj (w q.2.2)) *
        phase (q.2.1-q.2.2) (T q.2.1-T q.2.2) q.1) (volume.prod (μ.prod ν)) := by
  apply ((hχ.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_fst (μ.prod ν)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold phase
    fun_prop
  · filter_upwards [] with q
    simp only [norm_mul, Complex.norm_conj, norm_phase, mul_one, pow_two]
    have hww : ‖w q.2.1‖ * ‖w q.2.2‖ ≤ 1 := by
      nlinarith [hb q.2.1, hb q.2.2, norm_nonneg (w q.2.1), norm_nonneg (w q.2.2)]
    nlinarith [mul_self_nonneg ‖χ q.1‖]

lemma graphDual_pairing (χ : Plane → ℂ) (hχm : Measurable χ)
    (hχ : MemLp χ 2 volume) (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    (∫ ξ, graphDual χ μ T w ξ * conj (graphDual χ ν T w ξ)) =
      ∫ z : Plane × Plane, w z.1 * conj (w z.2) *
        frequencyKernel χ (z.1-z.2) (T z.1-T z.2) ∂μ.prod ν := by
  have hp (ξ : Plane) : graphDual χ μ T w ξ * conj (graphDual χ ν T w ξ) =
      ∫ z : Plane × Plane, χ ξ * conj (χ ξ) * (w z.1 * conj (w z.2)) *
        phase (z.1-z.2) (T z.1-T z.2) ξ ∂μ.prod ν := by
    simp only [graphDual, graphFourier, map_mul]
    rw [← integral_conj]
    rw [show (χ ξ * (∫ x, w x * phase x (T x) ξ ∂μ)) *
        (conj (χ ξ) * (∫ x, conj (w x * phase x (T x) ξ) ∂ν)) =
        (χ ξ * conj (χ ξ)) * ((∫ x, w x * phase x (T x) ξ ∂μ) *
        (∫ x, conj (w x * phase x (T x) ξ) ∂ν)) by ring]
    rw [← integral_prod_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [map_mul, ← phase_mul_conj]
    ring
  simp_rw [hp]
  rw [integral_integral_swap (integrable_graph_pairing χ hχm hχ μ ν hT hw hb)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [frequencyKernel, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

lemma norm_graphDual_pairing_le (χ : Plane → ℂ) (hχm : Measurable χ)
    (hχ : MemLp χ 2 volume) (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {B : ℝ}
    (hK : ∀ᵐ z : Plane × Plane ∂μ.prod ν,
      ‖frequencyKernel χ (z.1-z.2) (T z.1-T z.2)‖ ≤ B) :
    ‖∫ ξ, graphDual χ μ T w ξ * conj (graphDual χ ν T w ξ)‖ ≤
      B * μ.real univ * ν.real univ := by
  rw [graphDual_pairing χ hχm hχ μ ν hT hw hb]
  have hbound : ∀ᵐ z : Plane × Plane ∂μ.prod ν,
      ‖w z.1 * conj (w z.2) * frequencyKernel χ (z.1-z.2) (T z.1-T z.2)‖ ≤ B := by
    filter_upwards [hK] with z hz
    simp only [norm_mul, Complex.norm_conj]
    have hwprod : ‖w z.1‖ * ‖w z.2‖ ≤ 1 := by
      nlinarith [hb z.1, hb z.2, norm_nonneg (w z.1), norm_nonneg (w z.2)]
    exact (mul_le_mul_of_nonneg_right hwprod (norm_nonneg _)).trans (by simpa using hz)
  have hh := norm_integral_le_of_norm_le_const hbound
  have hm : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using (measureReal_prod_prod (μ := μ) (ν := ν) univ univ)
  simpa only [hm, mul_assoc] using hh

lemma frequencyKernel_scaled (χ : Plane → ℂ) (N : ℝ) (z : Plane) (t : ℝ) :
    frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t =
      EndpointKernel.scaledKernel (fun ξ => χ ξ * conj (χ ξ)) N z t := by
  unfold frequencyKernel EndpointKernel.scaledKernel
  congr 1
  funext ξ
  rw [phase_eq_kernel_oscillation]

lemma frequencyKernel_time_decay {χ : Plane → ℂ} {c : ℝ}
    (hc : 0 < c) (hχ : ContDiff ℝ ∞ χ) (hcomp : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c ≤ ‖ξ‖) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ (z : Plane) (t : ℝ),
      ‖z‖ ≤ c * N * |t| →
      (N^2 * |t|)^k * ‖frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t‖ ≤ C * N^2 := by
  have hs : ContDiff ℝ ∞ (fun ξ => χ ξ * conj (χ ξ)) := by exact hχ.mul (Complex.conjCLE.contDiff.comp hχ)
  obtain ⟨C,hC,hK⟩ := EndpointKernel.scaledKernel_time_decay hc hs hcomp.mul_right
    (fun ξ hξ => hann ξ (tsupport_mul_subset_left hξ)) k
  exact ⟨C,hC,fun N hN z t hz => by rw [frequencyKernel_scaled]; exact hK N hN z t hz⟩

lemma frequencyKernel_spatial_decay {χ : Plane → ℂ} {R : ℝ}
    (hR : 0 < R) (hχ : ContDiff ℝ ∞ χ) (hcomp : HasCompactSupport χ)
    (hsupp : ∀ ξ ∈ tsupport χ, ‖ξ‖ ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ (z : Plane) (t : ℝ),
      4 * R * N * |t| ≤ ‖z‖ →
      ‖frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t‖ ≤ C * N^2 / (1+N*‖z‖)^k := by
  have hs : ContDiff ℝ ∞ (fun ξ => χ ξ * conj (χ ξ)) := by exact hχ.mul (Complex.conjCLE.contDiff.comp hχ)
  obtain ⟨C,hC,hK⟩ := EndpointKernel.scaledKernel_spatial_decay hR hs hcomp.mul_right
    (fun ξ hξ => hsupp ξ (tsupport_mul_subset_left hξ)) k
  exact ⟨C,hC,fun N hN z t hz => by rw [frequencyKernel_scaled]; exact hK N hN z t hz⟩

def graphLp (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) : L2 :=
  (graphDual_memLp χ hχ μ hT hw hb).toLp (graphDual χ μ T w)

lemma graphLp_ae (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    ⇑(graphLp χ hχ μ T w hT hw hb) =ᵐ[volume] graphDual χ μ T w :=
  MemLp.coeFn_toLp _

lemma inner_graphLp (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    inner ℂ (graphLp χ hχ ν T w hT hw hb) (graphLp χ hχ μ T w hT hw hb) =
      ∫ ξ, graphDual χ μ T w ξ * conj (graphDual χ ν T w ξ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [graphLp_ae χ hχ μ T w hT hw hb, graphLp_ae χ hχ ν T w hT hw hb] with ξ hμ hν
  simp only [hμ, hν, RCLike.inner_apply]

lemma graphLp_add_measure (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    graphLp χ hχ (μ+ν) T w hT hw hb =
      graphLp χ hχ μ T w hT hw hb + graphLp χ hχ ν T w hT hw hb := by
  apply Lp.ext
  filter_upwards [graphLp_ae χ hχ (μ+ν) T w hT hw hb,
    graphLp_ae χ hχ μ T w hT hw hb, graphLp_ae χ hχ ν T w hT hw hb,
    Lp.coeFn_add (graphLp χ hχ μ T w hT hw hb) (graphLp χ hχ ν T w hT hw hb)] with ξ hh hμ hν hadd
  rw [hadd, Pi.add_apply, hh, hμ, hν]
  unfold graphDual graphFourier
  rw [integral_add_measure (integrable_graph_phase μ hT hw hb ξ)
    (integrable_graph_phase ν hT hw hb ξ), mul_add]

lemma graphLp_zero_measure (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) : graphLp χ hχ 0 T w hT hw hb = 0 := by
  apply Lp.ext
  filter_upwards [graphLp_ae χ hχ 0 T w hT hw hb, Lp.coeFn_zero ℂ 2 volume] with ξ hh hz
  simp only [hh, hz, graphDual, graphFourier, integral_zero_measure, mul_zero, Pi.zero_apply]

lemma graphLp_finsetSum_measure {ι : Type*} (s : Finset ι) (χ : Plane → ℂ)
    (hχ : MemLp χ 2 volume) (μ : ι → Measure Plane) [∀ i, IsFiniteMeasure (μ i)]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    graphLp χ hχ (∑ i ∈ s, μ i) T w hT hw hb = ∑ i ∈ s, graphLp χ hχ (μ i) T w hT hw hb := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using graphLp_zero_measure χ hχ T w hT hw hb
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [graphLp_add_measure, ih]

end PlanarEndpoint
end

end OAI
