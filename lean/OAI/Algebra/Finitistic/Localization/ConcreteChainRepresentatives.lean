import OAI.Algebra.Finitistic.Localization.BoundedRepresentatives
import OAI.Algebra.Finitistic.Localization.SourceLinear
import OAI.Algebra.Finitistic.Localization.ChainRepresentatives

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ConcreteChainRepresentatives
open SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

abbrev representative (X : K P) : CochainComplex (Proj P) ℤ := X.obj.as

theorem representative_bounded (X : K P) :
    BoundedHomotopy.boundedComplex (Proj P) (representative P X) :=
  (BoundedHomotopy.bounded_quotient_obj_iff _ _).1 X.property

/-- The lifted source diagram has genuine bounded projective chain representatives
and a specified null-homotopy for every relation; no chain representatives are assumed. -/
theorem quadratic_representatives (na nb nr : ℕ) (X₀ X₁ X₂ : K P)
    (a : Fin na → (X₀ ⟶ X₁)) (b : Fin nb → (X₁ ⟶ X₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ r, ∑ i, ∑ j, c r i j • (a i ≫ b j) = 0) :
    ∃ (f : Fin na → (representative P X₀ ⟶ representative P X₁))
      (g : Fin nb → (representative P X₁ ⟶ representative P X₂)),
      (∀ i, (HomotopyCategory.quotient (Proj P) (.up ℤ)).map (f i) = (a i).hom) ∧
      (∀ j, (HomotopyCategory.quotient (Proj P) (.up ℤ)).map (g j) = (b j).hom) ∧
      Nonempty (∀ r, Homotopy (∑ i, ∑ j, c r i j • (f i ≫ g j)) 0) := by
  let I := (BoundedHomotopy.bounded (Proj P)).ι
  apply ChainRepresentatives.quadratic_chain_representatives na nb nr
    (representative P X₀) (representative P X₁) (representative P X₂)
    (fun i => I.map (a i)) (fun j => I.map (b j)) c
  intro r
  have h := congrArg I.map (hc r)
  simp only [Functor.map_sum,Functor.map_smul,Functor.map_comp,Functor.map_zero] at h
  exact h
end LittleFinitistic.ConcreteChainRepresentatives

end

end OAI
