import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {X : ModuleCat.{u} R}

theorem scalar_end_hom (M : ModuleCat.{u} R) (f : M ⟶ M) (c : k)
    (hf : ∀ x : M, f.hom x = (algebraMap k R c) • x) : f = c • (𝟙 M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hf x

theorem extZero_scalar_of_hom
    (h : ∀ f : X ⟶ X, ∃ c : k, f = c • 𝟙 X) (x : Ext X X 0) :
    ∃ c : k, x = c • Ext.mk₀ (𝟙 X) := by
  obtain ⟨c,hc⟩ := h (Ext.homEquiv₀ x)
  refine ⟨c, ?_⟩
  exact (Ext.mk₀_homEquiv₀_apply x).symm.trans
    ((congrArg Ext.mk₀ hc).trans (Ext.mk₀_smul (R := k) c (𝟙 X)))

private theorem commute_step (a b : Ext X X 3) (n : ℕ) (x : Ext X X (3*n))
    (hab : a.comp b rfl = b.comp a rfl)
    (hax : a.comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp a (by omega : 3*n+3=3*(n+1))) :
    a.comp (b.comp x (by omega : 3+3*n=3*(n+1))) (by omega : 3+3*(n+1)=3*(n+2)) =
      (b.comp x (by omega : 3+3*n=3*(n+1))).comp a
        (by omega : 3*(n+1)+3=3*(n+2)) := by
  rw [← Ext.comp_assoc a b x rfl (by omega : 3+3*n=3*(n+1)) (by omega)]
  rw [hab]
  rw [Ext.comp_assoc b a x rfl (by omega : 3+3*n=3*(n+1)) (by omega)]
  rw [hax]
  rw [← Ext.comp_assoc b x a (by omega : 3+3*n=3*(n+1))
    (by omega : 3*n+3=3*(n+1)) (by omega)]

theorem cubicCentral_of_generation (a b : Ext X X 3)
    (hab : a.comp b rfl = b.comp a rfl)
    (hzero : ∀ x : Ext X X 0,
      a.comp x (by omega : 3+0=3) = x.comp a (by omega : 0+3=3) ∧
      b.comp x (by omega : 3+0=3) = x.comp b (by omega : 0+3=3))
    (hgen : ∀ (n : ℕ) (x : Ext X X (3*(n+1))), ∃ u v : Ext X X (3*n),
      x = a.comp u (by omega) + b.comp v (by omega)) :
    ∀ (n : ℕ) (x : Ext X X (3*n)),
      a.comp x (by omega : 3+3*n=3*(n+1)) = x.comp a (by omega) ∧
      b.comp x (by omega : 3+3*n=3*(n+1)) = x.comp b (by omega) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro x
    obtain ⟨u,v,rfl⟩ := hgen n x
    constructor
    · rw [Ext.comp_add, Ext.add_comp]
      exact congrArg₂ (· + ·) (commute_step a a n u rfl (ih u).1)
        (commute_step a b n v hab (ih v).1)
    · rw [Ext.comp_add, Ext.add_comp]
      exact congrArg₂ (· + ·) (commute_step b a n u hab.symm (ih u).2)
        (commute_step b b n v rfl (ih v).2)

end ArExplicit.ResolutionProducts

end

end OAI
