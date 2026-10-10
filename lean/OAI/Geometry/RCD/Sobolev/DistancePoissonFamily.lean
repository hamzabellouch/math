import OAI.Geometry.RCD.Sobolev.DistancePoissonConstruction
import OAI.Geometry.RCD.Coordinates.NormalizedDirichletError

namespace OAI

/-! # Actual distance-source Poisson families and their normalized errors -/

open Set Metric MeasureTheory Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

structure DistancePoissonFamily (n : ℕ) (κ B J C : ℝ)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k) where
  source : ℕ → Measure X
  finite : ∀ k, IsFiniteMeasure (source k)
  cutoff : ∀ k, GoodLaplacianCutoff μ Q (p k) (4*r k) C
  replacement : ℕ → SobolevSpace μ Q
  eikonal : ∀ k, ∀ᵐ x ∂μ.restrict (ball (p k) (4*r k)),
    localGamma μ Q (inwardSobolev μ Q (p k) (4*r k))
      (inwardSobolev μ Q (p k) (4*r k)) x=1
  defect : ∀ k (ψ : SobolevSpace μ Q) (v : X → ℝ) (L : ℝ≥0),
    LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball (p k) (r k) →
    SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
    energyForm μ Q (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k)) ψ+
      ((n:ℝ)+κ*(4*r k)^2)*(∫ x in ball (p k) (r k), v x ∂μ)=∫ x, v x ∂source k
  boundary : ∀ k, replacement k-positiveSquaredDistance μ Q
    (mul_nonneg (by norm_num) (hr k).le) (cutoff k) ∈ SobolevSpace.dirichlet μ Q (ball (p k) (r k))
  laplacian : ∀ k, IsConstantLaplacianOn μ Q (ball (p k) (r k))
    (replacement k) ((n:ℝ)+κ*(4*r k)^2)
  height : ∀ k, ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q
    (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k)-replacement k) x ∧
    SobolevSpace.toLp μ Q
      (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k)-replacement k) x≤B*(r k)^2
  energy_error : ∀ k, (∫ x, (SobolevSpace.minimalSlope μ Q
    (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k)-replacement k) x)^2 ∂μ)
      ≤(source k).real (ball (p k) (r k))*(B*(r k)^2)
  density_error : ∀ k, (∫ x in ball (p k) (r k),
    |(1/2:ℝ)*localGamma μ Q (replacement k) (replacement k) x-
      (1/2:ℝ)*localGamma μ Q
        (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k))
        (positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (cutoff k)) x| ∂μ)
      ≤(J+B/2)*(r k)^2*(source k).real (ball (p k) (r k))

namespace DistancePoissonFamily
variable {μ Q} {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  (F : DistancePoissonFamily μ Q n κ B J C p r hr)

def datum (k : ℕ) : SobolevSpace μ Q :=
  positiveSquaredDistance μ Q (mul_nonneg (by norm_num) (hr k).le) (F.cutoff k)

theorem normalized_value_error_tendsto_zero {P : ℝ} (hP : 0≤P)
    (hvol : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hpoin : ∀ k, ∀ v : SobolevSpace.dirichlet μ Q (ball (p k) (r k)),
      ‖SobolevSpace.toLp μ Q v.val‖^2≤P*(r k)^2*energyForm μ Q v.val v.val)
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => ‖normalizeLocalL2 μ (ball (p k) (r k))
      (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (p k) (r k)).measure_lt_top))
      (SobolevSpace.restrictLp μ Q (ball (p k) (r k))
        (((r k)^2)⁻¹ • (F.datum k-F.replacement k)))‖) atTop (𝓝 0) := by
  apply normalized_dirichlet_error_tendsto_zero μ Q (fun k => ball (p k) (r k))
    (fun k => ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (p k) (r k)).measure_lt_top)) hvol r
    (fun k => B*((F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k))))
    hP hr (fun k => F.datum k-F.replacement k)
  · intro k
    simpa only [datum,neg_sub] using (SobolevSpace.dirichlet μ Q (ball (p k) (r k))).neg_mem (F.boundary k)
  · exact hpoin
  · intro k
    apply (F.energy_error k).trans_eq
    field_simp [(hvol k).ne']
  · simpa only [mul_zero] using hmass.const_mul B

end DistancePoissonFamily
end RegularPointCoordinates

end

end OAI
