import OAI.Analysis.PlanarPacking.ContactData
import OAI.Analysis.PlanarPacking.CoupledFull

namespace OAI

/-!
# The exact contact interpolation solution

The inverse interpolation operator determines the coefficient lists for the prescribed contacts.
-/

namespace SharpPlanar
noncomputable def exactList₁ : X := coupledLeft g₁ g₂
noncomputable def exactList₂ : X := coupledRight g₁ g₂
lemma exactLists_equations : exactList₁-S exactList₂=g₁ ∧ exactList₂-S exactList₁=g₂ :=
  coupled_equations g₁ g₂
lemma exactLists_unique {x₁ x₂ : X} (h₁ : x₁-S x₂=g₁) (h₂ : x₂-S x₁=g₂) :
    x₁=exactList₁ ∧ x₂=exactList₂ := coupled_unique h₁ h₂
end SharpPlanar

end OAI
