import OAI.Geometry.RCD.Metric.ContainingMassUniformL2
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance
import OAI.Geometry.RCD.Harmonic.HarmonicModelCompactness

namespace OAI

/-! # Local value comparison with a compact extension of the limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.local_uniform_difference_l2 {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S R T : ℝ} (hS : 0<S)
    (hRT : R<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g F : Euclidean n → ℝ) (heq : EqOn F g (closedBall 0 T))
    (hw : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (R*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ)
    (hq : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-F (V k x)|≤δ) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k-q k) x)^2 ∂hausdorff n X)
      atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Ω := fun k => ball (p k) (R*r k)
  let m := fun k => μ.real (ball (p k) (S*r k))
  let z := fun k x => SobolevSpace.toLp μ hX.quadratic (w k-q k) x
  let : ∀ k, IsFiniteMeasure (μ.restrict (Ω k)) := fun k => ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (Ω k) isBounded_ball⟩
  have hsub (k : ℕ) : Ω k⊆ball (p k) (S*r k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (hRT.trans hTS).le (hr k).le)
  apply containing_mass_uniform_l2 (fun k => μ.restrict (Ω k)) m
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => by
      simp only [Measure.real,Measure.restrict_apply_univ]
      exact ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne (measure_mono (hsub k)))
    z (fun k => (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hX.quadratic (w k-q k))).mono_measure
      Measure.restrict_le_self)
  intro δ hδ
  have hsmall : ∀ᶠ k in atTop, ε k<(T-R)/2 :=
    hεlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hw (δ/2) (half_pos hδ),hq (δ/2) (half_pos hδ),hsmall] with k hwk hqk hek
  filter_upwards [hwk,ae_restrict_of_ae_restrict_of_subset (hsub k) hqk,
    ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp μ hX.quadratic (w k)) (SobolevSpace.toLp μ hX.quadratic (q k)))]
    with x hwx hqx hx hsubx
  have hd := (abs_le.mp (pointed_radial_distance (hr k) hS.le (hV k).metric (hsub k hx).le)).2
  have hxR : dist x (p k)/r k<R := (div_lt_iff₀ (hr k)).mpr hx
  have hxT : V k x∈closedBall 0 T := by
    rw [mem_closedBall,dist_zero_right]
    linarith
  rw [heq hxT] at hqx
  change |SobolevSpace.toLp μ hX.quadratic (w k-q k) x|≤δ
  rw [map_sub,hsubx,Pi.sub_apply]
  calc
    _ = |(SobolevSpace.toLp μ hX.quadratic (w k) x-g (V k x))-
        (SobolevSpace.toLp μ hX.quadratic (q k) x-g (V k x))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ δ := by linarith

end RegularPointCoordinates

end

end OAI
