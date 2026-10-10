import OAI.Geometry.NodalSets.Coefficients.SeedCoefficientNeighborhood
import OAI.Geometry.NodalSets.Elliptic.PositiveContravariant
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateCube

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

theorem seed_envelope_coordinate_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧ IsCompact (seedCoordinateCube a) ∧
    seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
      (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
        α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        let g := coefficientMetricValue ∘ c
        let p := localMetricGradient g seedRealChart y
        let H := localMetricHessian g seedRealChart y
        (∀ v : BaseModel, v ≠ 0 → 0 < g y v v) ∧ p ≠ 0 ∧
        ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
          0 < H p p + (g y p p+4)*H t t := by
  obtain ⟨r,δ,hr,hδ,hK,hbranch,hpersist⟩ := seed_uniform_coefficient_neighborhood
  have hcub : seedCoordinateCube (r/4) ⊆ ball (0 : BaseModel) r := by
    intro y hy
    rw [mem_ball,dist_zero_right]
    have hn := seedCoordinateCube_norm (a := r/4) (by positivity) hy
    linarith
  refine ⟨r,r/4,δ,hr,by positivity,hδ,hK,seedCoordinateCube_compact (by positivity),hcub,hbranch,?_⟩
  intro c hc hA hρ hclose y hy
  have ha := hpersist c hclose y hy
  rw [coefficientMetricJet_actual c y (hc y hy)
    (positiveContravariantEquiv (c y).1 (hA y hy)) rfl] at ha
  refine ⟨fun v hv ↦ coefficientMetric_positive (c y) (hA y hy) (hρ y hy) v hv,?_⟩
  exact (jetAdmissible_actual (coefficientMetricValue ∘ c) seedRealChart y).mp ha

end
end Yau.Target

end OAI
