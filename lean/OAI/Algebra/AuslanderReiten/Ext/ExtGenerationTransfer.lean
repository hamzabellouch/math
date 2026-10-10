import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {R : Type u} [Ring R] {X : ModuleCat.{u} R}
variable {D₀ D₁ : Type u} [AddCommGroup D₀] [AddCommGroup D₁]

theorem generationOfAddEquiv {n : ℕ} (a b : Ext X X 3)
    (e₀ : Ext X X n ≃+ D₀) (e₁ : Ext X X (n+3) ≃+ D₁)
    (f g : D₀ → D₁)
    (ha : ∀ x, e₁ (a.comp x (by omega)) = f (e₀ x))
    (hb : ∀ x, e₁ (b.comp x (by omega)) = g (e₀ x))
    (hgen : ∀ z : D₁, ∃ u v, z = f u + g v)
    (x : Ext X X (n+3)) :
    ∃ u v : Ext X X n, x = a.comp u (by omega) + b.comp v (by omega) := by
  obtain ⟨u,v,huv⟩ := hgen (e₁ x)
  refine ⟨e₀.symm u,e₀.symm v,e₁.injective ?_⟩
  rw [map_add,ha,hb,AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  exact huv

end ArExplicit.ResolutionProducts

end

end OAI
