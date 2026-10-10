import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity
import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def blowupBundle (I : X.IdealSheafData) (A : LineBundle X) :
    LineBundle (PiExponentSeshadri.BlowupGluing.scheme I) :=
  (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I).tensor
    (A.pullback (PiExponentSeshadri.BlowupGluing.projection I))

theorem eventual_blowup_jetRestriction_surjective_of_section_comparison
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U
        (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
        (twistedIdeal I A n)
        (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact eventual_jetRestriction_surjective_of_ample_comparison
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.projection I ≫ p) I A (blowupBundle I A)
    hample U hU hcover hcomparison

end
end PiExponent.BlowupJetSurjectivity

end OAI
