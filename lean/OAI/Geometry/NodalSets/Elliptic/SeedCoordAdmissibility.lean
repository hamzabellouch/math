import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Elliptic.HessianLinearTransport
import OAI.Geometry.NodalSets.Elliptic.SeedEnvelopePatch

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def seedCoordEquiv : Coord ≃L[ℝ] BaseModel :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).symm

def seedCoordReal : Coord → ℝ := seedRealChart ∘ seedCoordEquiv

def seedCoordMetric (c : BaseModel → CoefficientPoint BaseModel) :
    Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ :=
  linearMetricField seedCoordEquiv (coefficientMetricValue ∘ c)

lemma seedRealChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedRealChart y := by
  exact (Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedImagChart y := by
  exact (Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

lemma seedCoordMetric_differentiable (c : BaseModel → CoefficientPoint BaseModel)
    (y : BaseModel) (hc : DifferentiableAt ℝ c y)
    (hA : ∀ α : BaseModel →L[ℝ] ℝ, α ≠ 0 → 0 < α ((c y).1 α)) :
    DifferentiableAt ℝ (coefficientMetricValue ∘ c) y :=
  ((coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 hA) rfl).differentiableAt
    (by simp)).comp y hc

theorem seed_envelope_Coord_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (seedCoordinateCube a) ∧ seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
      (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
        α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ x : Coord, seedCoordEquiv x ∈ closedBall (0 : BaseModel) r →
        let g := seedCoordMetric c
        let p := metricGradient g seedCoordReal x
        let H := sourceHessian g seedCoordReal x
        (∀ v : Coord, v ≠ 0 → 0 < g x v v) ∧ p ≠ 0 ∧
        ∃ t : Coord, g x p t = 0 ∧ g x t t = 1 ∧
          0 < H p p + (g x p p+4)*H t t := by
  obtain ⟨r,a,δ,hr,ha,hδ,_,hK,hsub,hbranch,hpatch⟩ := seed_envelope_coordinate_patch
  refine ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,?_⟩
  intro c hc hA hρ hclose x hx
  obtain ⟨hp,hn,had⟩ := hpatch c hc hA hρ hclose (seedCoordEquiv x) hx
  refine ⟨linearMetricField_positive seedCoordEquiv _ x hp,?_⟩
  exact linearMetricField_admissible seedCoordEquiv (coefficientMetricValue ∘ c) seedRealChart x hp
    (seedCoordMetric_differentiable c _ (hc _ hx) (hA _ hx))
    (seedRealChart_smoothAt (hbranch _ hx).1) hn had

end
end Yau.Target

end OAI
