import OAI.Algebra.Finitistic.Localization.SourceQuotientAction
import OAI.Algebra.Finitistic.Localization.ConcreteFixedDiagram

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.SelectedFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction

abbrev encoding := auxiliaryEncoding
abbrev P := encoding.relations
abbrev theta := SourceQuotientAction.theta encoding
abbrev e := selectionIdempotent 0
abbrev alpha := (selectionAutomorphism 1).toAlgHom
lemma idem : e*e=e := selectionIdempotent_square 0
lemma central (r : SelectionRing) : e*r=r*e := (selectionIdempotent_central 0 r).eq

local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q P)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q P)) :=
  hasBinaryBiproducts_of_finite_biproducts _

abbrev U := summand theta e idem
abbrev oddDouble := U ⊞ OddDouble.formalShift U 3
abbrev selectedAction := oddDoubleAction theta e idem central alpha

/-- All choices, arrows, relation-basis equations and equivariant identifications
for the actual selecting algebra. No evaluation module is a parameter. -/
structure Data where
  V0 : SourceVerdier.Q P
  rho : SelectionRing →ₐ[ℂ] End V0
  iso : (toKaroubi (SourceVerdier.Q P)).obj V0 ≅ oddDouble
  D0 : SourceVerdier.K P
  D1 : SourceVerdier.K P
  D2 : SourceVerdier.K P
  phi0 : (SourceVerdier.q P).obj D0 ≅ V0
  phi1 : (SourceVerdier.q P).obj D1 ≅ V0
  phi2 : (SourceVerdier.q P).obj D2 ≅ V0
  f : Fin (encoding.generators+1) → (D0 ⟶ D1)
  g : Fin (encoding.generators+1) → (D1 ⟶ D2)
  equivariant : ∀ r : SelectionRing,
    (toKaroubi (SourceVerdier.Q P)).map (rho r) ≫ iso.hom = iso.hom ≫ selectedAction r
  arrow01 : ∀ a, (SourceVerdier.q P).map (f a) ≫ phi1.hom =
    phi0.hom ≫ rho (arrow (generator encoding) a)
  arrow12 : ∀ b, (SourceVerdier.q P).map (g b) ≫ phi2.hom =
    phi1.hom ≫ rho (arrow (generator encoding) b)
  relations : ∀ r : RelationIndex P,
    ∑ a, ∑ b, basisCoefficient P r a b • (f a ≫ g b) = 0

/-- Choose once, using the proved native finite-diagram theorem and actual theta. -/
def fixed : Data := Classical.choice (by
  obtain ⟨V,rho,i,D0,D1,D2,p0,p1,p2,f,g,he,hf,hg,hr⟩ :=
    ConcreteFixedDiagram.fixed_diagram encoding theta e idem central alpha
  exact ⟨⟨V,rho,i,D0,D1,D2,p0,p1,p2,f,g,he,hf,hg,hr⟩⟩)

theorem fixed_relations (r : RelationIndex P) :
    ∑ a, ∑ b, basisCoefficient P r a b • (fixed.f a ≫ fixed.g b) = 0 := fixed.relations r

theorem fixed_equivariant (r : SelectionRing) :
    (toKaroubi (SourceVerdier.Q P)).map (fixed.rho r) ≫ fixed.iso.hom =
      fixed.iso.hom ≫ selectedAction r := fixed.equivariant r
end LittleFinitistic.SelectedFixedDiagram

end

end OAI
