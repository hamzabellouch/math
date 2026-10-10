import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileCoordinates

namespace OAI

/-! The five leading profiles depend smoothly on the second jet, its first
transverse derivative, and the periodic parameter. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

abbrev LeadingProfileInput := (LowJet × ℝ) × LowJet

def leadingVelocity (z : LowJet × ℝ) : RealModes.RVec 4 := tangent z.1+l.velocity z

def leadingProfileMap (z : LeadingProfileInput) : EuclideanBoundaryProfile :=
  ![JetVelocityCoordinates.toEuclidean (l.leadingVelocity z.1),
    JetVelocityCoordinates.toEuclidean (slot 2 z.1.1),
    JetVelocityCoordinates.toEuclidean (slot 6 z.1.1),
    JetVelocityCoordinates.toEuclidean (fderiv ℝ l.leadingVelocity z.1 (z.2,0)),
    JetVelocityCoordinates.toEuclidean (fderiv ℝ l.velocity z.1 (0,1))]

lemma leadingVelocity_smooth : ContDiffOn ℝ ∞ l.leadingVelocity (O ×ˢ univ) :=
  (l.smoothTangent.comp contDiffOn_fst (fun _ hz => hz.1)).add l.smoothVelocity

lemma leadingProfileMap_smooth :
    ContDiffOn ℝ ∞ l.leadingProfileMap ((O ×ˢ univ) ×ˢ univ) := by
  have hJ : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => z.1.1) ((O ×ˢ univ) ×ˢ univ) :=
    contDiffOn_fst.fst
  have hV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) :=
    l.leadingVelocity_smooth.comp contDiffOn_fst (fun _ hz => hz.1)
  have hdV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.leadingVelocity_smooth.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by simp)).comp contDiffOn_fst (fun _ hz => hz.1)
  have hdW : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.velocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.smoothVelocity.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by simp)).comp contDiffOn_fst (fun _ hz => hz.1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn hV
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 2).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 6).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdV.clm_apply (contDiffOn_snd.prodMk contDiffOn_const))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdW.clm_apply contDiffOn_const)

lemma leadingProfileMap_continuousAt {z : LeadingProfileInput} (hz : z.1.1 ∈ O) :
    ContinuousAt l.leadingProfileMap z :=
  (l.leadingProfileMap_smooth.contDiffAt
    (((O.isOpen.prod isOpen_univ).prod isOpen_univ).mem_nhds
      ⟨⟨hz,mem_univ _⟩,mem_univ _⟩)).continuousAt

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
