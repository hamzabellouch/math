import OAI.Geometry.SurfaceImmersion.Primitive.CircularProfilePullback
import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileStability

namespace OAI

/-! Circular profiles of the actual original immersion, expressed through
its second jet and its transverse third derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_geometricLeadingProfile {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period)) =
      circularFamilyProfile (tangent ∘ lowJet G) ((slot 1) ∘ lowJet G)
        ((slot 2) ∘ lowJet G) ((slot 6) ∘ lowJet G) (R ∘ lowJet G)
        (e₁ ∘ lowJet G) (e₂ ∘ lowJet G) (fun z => α (lowJet G z.1,z.2))
        (coordinateVector 1) (p,t) := by
  have hj := hGO hp
  have he : l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period) =
      l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) :=
    (l.leadingProfileMap_geometry hG hGO hp t).symm
  rw [he,l.circular_leadingProfileMap hR h₁ h₂ hα hvel hj]
  have hQ : DifferentiableAt ℝ tangent (lowJet G p) :=
    (l.smoothTangent.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by simp)
  have hh := circularFamilyProfile_comp (t := t) (X := slot 1) (Y := slot 2) (C := slot 6)
    ((lowJet_smooth hG).differentiable (by simp) p) hQ
    ((hR.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by simp))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by simp))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by simp))
    ((hα.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds ⟨hj,mem_univ t⟩)).differentiableAt (by simp))
    (coordinateVector 1)
  rw [lowJet_derivative hG] at hh
  exact hh.symm

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
