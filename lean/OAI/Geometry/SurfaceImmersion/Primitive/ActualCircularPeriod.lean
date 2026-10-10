import OAI.Geometry.SurfaceImmersion.Primitive.ActualCircularProfile

namespace OAI

/-! Representatives in one compact period transfer the constructed surface
profile estimates to the analytic loop at every phase. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation SurfaceJetCoordinates
open JetVelocityCoordinates

lemma actual_circular_period_profile {F : SmallModes.Base → Vec} (hF : ContDiff ℝ ∞ F)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (F ∘ baseEquiv)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : CovarianceCorrector.Period) :
    ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧
      boundaryProfileMap (l.geometricLeadingProfile (F ∘ baseEquiv) (hF.comp baseEquiv.contDiff)
        hGO p t) = surfaceCircularProfile F a e₁ e₂ α (baseEquiv p,s) := by
  have ht : t ∈ ((↑) : ℝ → CovarianceCorrector.Period) '' Icc (0 : ℝ) (0+1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨s,hs,hst⟩ := ht
  refine ⟨s,by simpa only [zero_add] using hs,?_⟩
  rw [← hst]
  exact l.actual_circular_geometric_profile hF ha hOZ hamp h₁ h₂ hα hvel hGO hp s

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
