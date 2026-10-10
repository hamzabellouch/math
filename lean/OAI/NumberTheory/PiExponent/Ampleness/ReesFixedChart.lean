import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart
import OAI.NumberTheory.PiExponent.Ampleness.ReesProductFrames

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem exists_coordinateRing : ∃ C : CommRingCat, C = CommRingCat.of (Chart I a s) := ⟨_,rfl⟩
def coordinateRing : CommRingCat := (exists_coordinateRing I a s).choose
omit [Fintype J] [DecidableEq J] in
theorem coordinateRing_eq : coordinateRing I a s = CommRingCat.of (Chart I a s) :=
  (exists_coordinateRing I a s).choose_spec

def coordinateEquiv : coordinateRing I a s ≃+* Chart I a s :=
  (eqToIso (coordinateRing_eq I a s)).commRingCatIsoToRingEquiv

private abbrev coordinateInv : CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s :=
  CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom

def base : R →+* coordinateRing I a s :=
  (coordinateInv I a s).hom.comp (ReesProductChart.chartBase I a s)

instance coordinateInv_isIso :
    IsIso (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
    CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) := by
  change IsIso (eqToIso (coordinateRing_eq I a s)).inv
  infer_instance

private local instance coordinateSpec_isIso :
    IsIso (Spec.map (coordinateInv I a s)) :=
  inferInstanceAs (IsIso
    (Scheme.Spec.mapIso (eqToIso (coordinateRing_eq I a s)).symm.op).hom)

variable {s} (hs : s.Nonempty)
def chart : Spec (coordinateRing I a s) ⟶ affineBlowup I :=
  Spec.map (coordinateInv I a s) ≫
    ReesProductPowerSections.chartMorphism I a hs

instance : IsOpenImmersion (chart I a hs) := by
  exact IsOpenImmersion.comp _ _

theorem chart_projection :
    chart I a hs ≫ projection I = Spec.map (CommRingCat.ofHom (base I a s)) := by
  rw [chart, Category.assoc, ReesProductPowerSections.chartMorphism_projection]
  exact (Spec.map_comp
    (show CommRingCat.of R ⟶ CommRingCat.of (Chart I a s) from
      CommRingCat.ofHom (ReesProductChart.chartBase I a s))
    (coordinateInv I a s)).symm

theorem chart_opensRange :
    (chart I a hs).opensRange = (ReesProductPowerSections.chartMorphism I a hs).opensRange :=
  Scheme.Hom.opensRange_comp_of_isIso _ _

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chart I a hs).opensRange, isAffineOpen_opensRange _⟩

theorem chartOpen_eq :
    (chartOpen I a hs).1 = (ReesProductPowerSections.chartOpen I a hs).1 :=
  chart_opensRange I a hs

end
end PiExponent.ReesFrozenChart

end OAI
