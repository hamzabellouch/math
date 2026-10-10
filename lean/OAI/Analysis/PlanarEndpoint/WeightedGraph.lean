import OAI.Analysis.PlanarEndpoint.AnnularCutoff
import OAI.Analysis.PlanarEndpoint.DyadicGraph
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.GraphLocalization
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.TimeSeparation

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace PlanarEndpoint

lemma annularCutoff_scaled_memLp (j : ℕ) :
    MemLp (fun ξ => annularCutoff (((2:ℝ)^j)⁻¹ • ξ)) 2 volume :=
  scaled_cutoff_memLp annularCutoff annularCutoff_smooth.continuous
    annularCutoff_compact (pow_pos (by norm_num : (0:ℝ)<2) j)

def normalizedGraphDensity (j : ℕ) (μ : Measure Plane)
    (T : Plane → ℝ) (w : Plane → ℂ) (ξ : Plane) : ℂ :=
  (((2:ℝ)^j)^(-(1/3:ℝ))) •
    graphDual (fun η => annularCutoff (((2:ℝ)^j)⁻¹ • η)) μ T w ξ

lemma normalizedGraphDensity_memLp (j : ℕ) (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) : MemLp (normalizedGraphDensity j μ T w) 2 volume :=
  by
    exact (graphDual_memLp _ (annularCutoff_scaled_memLp j) μ hT hw hb).const_smul
      (((2:ℝ)^j)^(-(1/3:ℝ)))

lemma integral_sq_norm_toLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : X → ℂ} (hv : MemLp v 2 μ) : (∫ x, ‖v x‖^2 ∂μ) = ‖hv.toLp v‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]

lemma normalizedGraphDensity_energy (j : ℕ) (μ : Measure Plane) [IsFiniteMeasure μ]
    {T : Plane → ℝ} {w : Plane → ℂ} (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (ht : ∀ᵐ x ∂μ, T x ∈ Ico 0 1) :
    (∫ ξ, ‖normalizedGraphDensity j μ T w ξ‖^2) =
      ‖normalizedDyadicVector annularCutoff annularCutoff_smooth annularCutoff_compact
        j μ T w hT hw hb []‖^2 := by
  have hμ : μ.restrict (DyadicGraph.fiber T []) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by simpa [DyadicGraph.fiber] using ht)
  dsimp only [normalizedDyadicVector, DyadicGraph.vector]
  rw [graphLp_congr_measure _ _ hμ T w hT hw hb]
  simp only [normalizedGraphDensity, norm_smul, mul_pow, integral_const_mul]
  congr 1
  exact integral_sq_norm_toLp (graphDual_memLp _ (annularCutoff_scaled_memLp j) μ hT hw hb)

lemma sobolevWeight_inv_le_dyadic (j : ℕ) {ξ : Plane} (hξ : (2:ℝ)^j ≤ ‖ξ‖) :
    (sobolevWeight ξ)⁻¹ ≤ (((2:ℝ)^j)^(-(1/3:ℝ)))^2 := by
  have hN : 0 < (2:ℝ)^j := by positivity
  rw [sobolevWeight, ← Real.rpow_neg (by positivity), ← Real.rpow_mul_natCast hN.le]
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hN)
    (show ((2:ℝ)^j)^2 ≤ 1+‖ξ‖^2 by nlinarith [norm_nonneg ξ])
    (by norm_num : -(1/3:ℝ) ≤ 0)
  rw [← Real.rpow_natCast_mul hN.le] at hh
  convert hh using 1
  congr 1
  norm_num

lemma unit_ball_real (x : Plane) : volume.real (Metric.ball x 1) = Real.pi := by
  simp [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_nonneg]

lemma graphFourier_unit_bound (x₀ : Plane) {T : Plane → ℝ} {w : Plane → ℂ}
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1) (ξ : Plane) :
    ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖ ≤ Real.pi := by
  exact (norm_graphFourier_le _ hT hw hb ξ).trans_eq (by
    simp only [measureReal_def, Measure.restrict_apply_univ]
    exact unit_ball_real x₀)

def graphLowMajorant : Plane → ℝ :=
  (Metric.ball (0 : Plane) 1).indicator (fun _ => Real.pi^2)

lemma graphLowMajorant_nonneg (ξ : Plane) : 0 ≤ graphLowMajorant ξ := by
  exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) ξ

lemma graphLowMajorant_integrable : Integrable graphLowMajorant volume := by
  exact IntegrableOn.integrable_indicator
    (integrable_const (Real.pi^2) (μ := volume.restrict (Metric.ball (0:Plane) 1))) measurableSet_ball

lemma graphLowMajorant_integral : (∫ ξ, graphLowMajorant ξ) = Real.pi^3 := by
  rw [graphLowMajorant, integral_indicator measurableSet_ball, integral_const]
  simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  change volume.real (Metric.ball (0:Plane) 1)*Real.pi^2=Real.pi^3
  rw [unit_ball_real]
  ring

lemma graph_weighted_pointwise (x₀ : Plane) {T : Plane → ℝ} {w : Plane → ℂ}
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1)
    (n : ℕ) (ξ : Plane) (hξ : ‖ξ‖ < (2:ℝ)^n) :
    (sobolevWeight ξ)⁻¹*‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 ≤
      graphLowMajorant ξ + ∑ j ∈ Finset.range n,
        ‖normalizedGraphDensity j (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 := by
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range n,
      ‖normalizedGraphDensity j (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hsmall : ‖ξ‖ < 1
  · have hlow : graphLowMajorant ξ = Real.pi^2 := by
      rw [graphLowMajorant, indicator_of_mem (by simpa using hsmall)]
    rw [hlow]
    have hi : (sobolevWeight ξ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (sobolevWeight_one_le ξ)
    have hg := graphFourier_unit_bound x₀ hT hw hb ξ
    have hsq : ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 ≤ Real.pi^2 :=
      (sq_le_sq₀ (norm_nonneg _) Real.pi_nonneg).2 hg
    nlinarith [mul_le_mul_of_nonneg_right hi (sq_nonneg
      ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖)]
  · obtain ⟨j,hj,hj0,hj1⟩ := dyadic_annular_cover (le_of_not_gt hsmall) n hξ
    have hc := scaled_annularCutoff_one j ⟨hj0,hj1.le⟩
    have he : ‖normalizedGraphDensity j (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 =
        (((2:ℝ)^j)^(-(1/3:ℝ)))^2 *
          ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2 := by
      simp only [normalizedGraphDensity, graphDual, hc, one_mul, norm_smul, Real.norm_eq_abs,
        sq_abs, mul_pow]
    have hh := mul_le_mul_of_nonneg_right (sobolevWeight_inv_le_dyadic j hj0)
      (sq_nonneg ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖)
    rw [← he] at hh
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range n) =>
      sq_nonneg ‖normalizedGraphDensity j (volume.restrict (Metric.ball x₀ 1)) T w ξ‖)
      (Finset.mem_range.mpr hj)
    exact hh.trans (hs.trans (le_add_of_nonneg_left (graphLowMajorant_nonneg ξ)))

lemma graph_weighted_integrableOn (x₀ : Plane) {T : Plane → ℝ} {w : Plane → ℂ}
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1) (R : ℝ) :
    IntegrableOn (fun ξ => (sobolevWeight ξ)⁻¹ *
      ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2)
      (Metric.ball (0:Plane) R) volume := by
  have hc : Continuous (fun ξ => (sobolevWeight ξ)⁻¹ *
      ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2) :=
    (continuous_sobolevWeight.inv₀ (fun ξ => (sobolevWeight_pos ξ).ne')).mul
      ((continuous_graphFourier _ hT hw hb).norm.pow 2)
  exact (hc.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0:Plane) R)).mono_set
    Metric.ball_subset_closedBall

lemma graph_weighted_sum_bound {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ)
      (_ : Measurable T) (_ : Measurable w) (_ : ∀ x, ‖w x‖ ≤ 1),
      (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) → ∀ n : ℕ,
      (∫ ξ in Metric.ball (0:Plane) ((2:ℝ)^n), (sobolevWeight ξ)⁻¹ *
        ‖graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖^2) ≤ C := by
  obtain ⟨C,hC,hbnd⟩ := graph_square_sum_of_shortTime hp hshort
  refine ⟨Real.pi^3+C,by positivity,?_⟩
  intro x₀ T w hT hw hb ht n
  let μ := volume.restrict (Metric.ball x₀ 1)
  have hti : ∀ᵐ x ∂μ, T x ∈ Ico 0 1 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ht x hx
  have hsq (j : ℕ) : Integrable (fun ξ => ‖normalizedGraphDensity j μ T w ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (normalizedGraphDensity_memLp j μ hT hw hb).aestronglyMeasurable).1
      (normalizedGraphDensity_memLp j μ hT hw hb)
  have hmajor := graphLowMajorant_integrable.add (integrable_finsetSum (Finset.range n) (fun j _ => hsq j))
  rw [← integral_indicator measurableSet_ball]
  have hle := integral_mono ((graph_weighted_integrableOn x₀ hT hw hb _).integrable_indicator
    measurableSet_ball) hmajor (show ∀ ξ, _ ≤ _ from fun ξ => by
      by_cases hξ : ξ ∈ Metric.ball (0:Plane) ((2:ℝ)^n)
      · rw [indicator_of_mem hξ]
        exact graph_weighted_pointwise x₀ hT hw hb n ξ (by simpa using hξ)
      · rw [indicator_of_notMem hξ]
        exact add_nonneg (graphLowMajorant_nonneg ξ) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply hle.trans
  change (∫ ξ, graphLowMajorant ξ + ∑ j ∈ Finset.range n,
    ‖normalizedGraphDensity j μ T w ξ‖^2) ≤ Real.pi^3+C
  rw [integral_add graphLowMajorant_integrable (integrable_finsetSum (Finset.range n) (fun j _ => hsq j)),
    graphLowMajorant_integral, integral_finsetSum _ (fun j _ => hsq j)]
  simp_rw [normalizedGraphDensity_energy _ μ hT hw hb hti]
  exact add_le_add_right (hbnd x₀ T w hT hw hb ht n) _

end PlanarEndpoint
end

end OAI
