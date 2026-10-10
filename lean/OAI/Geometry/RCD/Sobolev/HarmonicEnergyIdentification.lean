import OAI.Geometry.RCD.Sobolev.HarmonicWeightedEnergyLimit
import OAI.Geometry.RCD.Metric.PointedWeightedDifference
import OAI.Geometry.RCD.Sobolev.PhysicalBallMeasuredTests

namespace OAI

/-! # Constant energy densities of the original sequence identify the limit -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_constant_energy_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k) ≤ M)
    (g : Euclidean n → ℝ) (hg : ContDiffOn ℝ ∞ g (ball 0 5))
    (hgL : ∀ W < 5, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)| ≤ δ)
    {C : ℝ}
    (herror : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-C|
        ∂hausdorff n X) atTop (𝓝 0))
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0 ≤ φ z) (hs : tsupport φ ⊆ ball 0 3) :
    (∫ z in ball (0 : Euclidean n) 5, φ z*‖fderiv ℝ g z‖^2) =
      C*(∫ z in ball (0 : Euclidean n) 5, φ z) := by
  let μ := hausdorff n X
  let c := fun k => (μ.real (ball (p k) (5*r k)))⁻¹
  have hm (k : ℕ) : 0 < μ.real (ball (p k) (5*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hc (k : ℕ) : 0 ≤ c k := inv_nonneg.mpr (hm k).le
  have hdiff := pointed_weighted_difference_tendsto μ (by norm_num : (0:ℝ)≤5)
    (by norm_num : (3:ℝ)<4) (by norm_num : (4:ℝ)≤5) p r ε c V hr hc hεlim
    (fun k => (hV k).metric) (fun k => (hV k).measurable)
    (fun k x => r k^2*localGamma μ hX.quadratic (w k) (w k) x) (fun _ _ => C)
    (fun k => ((localGamma_memL1 μ hX.quadratic (w k) (w k)).const_mul _).integrableOn)
    (fun k => integrableOn_const (hX.finiteOnBounded _ isBounded_ball).ne)
    herror φ ((subset_tsupport φ).trans hs)
  have henergy := hX.harmonic_weighted_energy_limit hn p r ε V hr hcurv hε hε1 hεlim
    hV w hw hM hnorm g hg hgL hconv φ hφ hs
  have hscalar := physical_ball_measured_test_tendsto (by norm_num : (0:ℝ)<5)
    (by norm_num : (0:ℝ)<5) le_rfl hr hV
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne) hm hεlim φ
  have he (k : ℕ) :
      c k*(∫ x in ball (p k) (5*r k), φ (V k x)*(r k^2*
        localGamma μ hX.quadratic (w k) (w k) x) ∂μ)-
      c k*(∫ x in ball (p k) (5*r k), φ (V k x)*C ∂μ) =
      r k^2*c k*(∫ x in ball (p k) (5*r k), φ (V k x)*
        localGamma μ hX.quadratic (w k) (w k) x ∂μ)-
      C*(c k*∫ x in ball (p k) (5*r k), φ (V k x) ∂μ) := by
    simp_rw [mul_left_comm (φ _) (r k^2)]
    rw [integral_const_mul,integral_mul_const]
    ring
  simp only [he] at hdiff
  have hlim := henergy.sub (hscalar.const_mul C)
  have heq := tendsto_nhds_unique hdiff hlim
  have hv : 0 < volume.real (ball (0 : Euclidean n) 5) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  have hh : (volume.real (ball (0 : Euclidean n) 5))⁻¹*
      ((∫ z in ball 0 5, φ z*‖fderiv ℝ g z‖^2)-C*(∫ z in ball 0 5, φ z))=0 := by
    nlinarith [heq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (inv_ne_zero hv.ne'))

end RegularPointCoordinates

end

end OAI
