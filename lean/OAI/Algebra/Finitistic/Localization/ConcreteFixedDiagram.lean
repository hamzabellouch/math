import OAI.Algebra.Finitistic.Localization.FixedDiagram
import OAI.Algebra.Finitistic.Localization.SourceShiftLinear
import OAI.Algebra.Finitistic.Encoding.RelationBasisAction

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.ConcreteFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)
local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- The fixed odd-double diagram in the actual Kᵇ(proj-B) and its actual Verdier
quotient. Every independent relation of the constructed path algebra is included. -/
theorem fixed_diagram {L : SourceVerdier.Q E.relations} (θ : R →ₐ[k] End L)
    (e : R) (he : e*e=e) (hec : ∀ r : R, e*r=r*e) (α : R →ₐ[k] R) :
    ∃ (V₀ : SourceVerdier.Q E.relations) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi (SourceVerdier.Q E.relations)).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3)
      (D₀ D₁ D₂ : SourceVerdier.K E.relations)
      (φ₀ : (SourceVerdier.q E.relations).obj D₀ ≅ V₀)
      (φ₁ : (SourceVerdier.q E.relations).obj D₁ ≅ V₀)
      (φ₂ : (SourceVerdier.q E.relations).obj D₂ ≅ V₀)
      (f : Fin (E.generators+1) → (D₀ ⟶ D₁))
      (g : Fin (E.generators+1) → (D₁ ⟶ D₂)),
      (∀ r : R, (toKaroubi (SourceVerdier.Q E.relations)).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hec α r) ∧
      (∀ a, (SourceVerdier.q E.relations).map (f a) ≫ φ₁.hom =
        φ₀.hom ≫ ρ₀ (arrow (generator E) a)) ∧
      (∀ b, (SourceVerdier.q E.relations).map (g b) ≫ φ₂.hom =
        φ₁.hom ≫ ρ₀ (arrow (generator E) b)) ∧
      (∀ r : RelationIndex E.relations,
        ∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b) = 0) :=
  FixedDiagram.fixed_diagram (SourceVerdier.q E.relations) (SourceVerdier.Sigma E.relations)
    θ e he hec α (E.generators+1) (E.generators+1)
    (Module.finrank k (QuadraticEncoding.relationSpace E.relations))
    (arrow (generator E)) (arrow (generator E)) (basisCoefficient E.relations)
    (encoding_basis_action E)
end LittleFinitistic.ConcreteFixedDiagram

end

end OAI
