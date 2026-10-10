import OAI.Geometry.SurfaceImmersion.Primitive.ActualCircularPeriod
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile

namespace OAI

/-! The analytic profile attached to an atlas phase chart is exactly one
of the real circular profiles used in the finite boundary construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation SurfaceVelocityFamily VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_comp_base (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base)
    (F : M → Space) : A.phaseRealChartMap i T F ∘ baseEquiv = A.jetChartMap i F ∘ T := by
  funext p
  simp only [Function.comp_apply,phaseRealChartMap,baseEquiv.symm_apply_apply]

private lemma geometric_profile_congr {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (l : Loop O) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G H : JetPolynomial.Base → JetPolynomial.Space} (he : G = H)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hGO : MapsTo (JetPolynomial.lowJet G) S O) (hHO : MapsTo (JetPolynomial.lowJet H) S O)
    (p : JetPolynomial.Base) (t : CovarianceCorrector.Period) :
    l.geometricLeadingProfile G hG hGO p t = l.geometricLeadingProfile H hH hHO p t := by
  subst H
  rfl

lemma phase_circular_geometric_profile (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (A.jetChartMap i F ∘ T)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile (A.jetChartMap i F ∘ T)
        ((A.jetChartMap_smooth i hF).comp hT) hGO p (t : CovarianceCorrector.Period)) =
      surfaceCircularProfile (A.phaseRealChartMap i T F) a e₁ e₂ α (baseEquiv p,t) := by
  have hcomp := A.phaseRealChartMap_comp_base i T F
  have hGO' : MapsTo (JetPolynomial.lowJet (A.phaseRealChartMap i T F ∘ baseEquiv)) S O := by
    simpa only [hcomp] using hGO
  have he := l.actual_circular_geometric_profile (A.phaseRealChartMap_smooth i hT hF)
    ha hOZ hamp h₁ h₂ hα hvel hGO' hp t
  have heq := geometric_profile_congr l hcomp
    ((A.phaseRealChartMap_smooth i hT hF).comp baseEquiv.contDiff)
    ((A.jetChartMap_smooth i hF).comp hT) hGO' hGO p (t : CovarianceCorrector.Period)
  exact (congrArg boundaryProfileMap heq).symm.trans he


lemma phase_circular_period_profile (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (A.jetChartMap i F ∘ T)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : CovarianceCorrector.Period) :
    ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧
      boundaryProfileMap (l.geometricLeadingProfile (A.jetChartMap i F ∘ T)
        ((A.jetChartMap_smooth i hF).comp hT) hGO p t) =
      surfaceCircularProfile (A.phaseRealChartMap i T F) a e₁ e₂ α (baseEquiv p,s) := by
  have hcomp := A.phaseRealChartMap_comp_base i T F
  have hGO' : MapsTo (JetPolynomial.lowJet (A.phaseRealChartMap i T F ∘ baseEquiv)) S O := by
    simpa only [hcomp] using hGO
  obtain ⟨s,hs,he⟩ := l.actual_circular_period_profile (A.phaseRealChartMap_smooth i hT hF)
    ha hOZ hamp h₁ h₂ hα hvel hGO' hp t
  have heq := geometric_profile_congr l hcomp
    ((A.phaseRealChartMap_smooth i hT hF).comp baseEquiv.contDiff)
    ((A.jetChartMap_smooth i hF).comp hT) hGO' hGO p t
  exact ⟨s,hs,(congrArg boundaryProfileMap heq).symm.trans he⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
