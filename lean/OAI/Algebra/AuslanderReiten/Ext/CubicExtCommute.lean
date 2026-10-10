import OAI.Algebra.AuslanderReiten.Ext.CubicExtAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f g : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ f n)
variable (hg : ∀ n, g (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ g n)

omit [HasDerivedCategory (ModuleCat.{u} R)] in
private theorem extMk_eq_of_map_eq {n : ℕ} (a b : P.complex.X n ⟶ X)
    (ha : P.complex.d (n+1) n ≫ a = 0) (hb : P.complex.d (n+1) n ≫ b = 0)
    (hab : a = b) : P.extMk a (n+1) rfl ha = P.extMk b (n+1) rfl hb := by
  subst b
  rfl

theorem cubic_endExt_commute (hfg : f 3 ≫ g 0 = g 3 ≫ f 0) :
    (endExt P (natCubicCocycle (k := k) P f hf)).comp
      (endExt P (natCubicCocycle (k := k) P g hg)) rfl =
    (endExt P (natCubicCocycle (k := k) P g hg)).comp
      (endExt P (natCubicCocycle (k := k) P f hf)) rfl := by
  have h₁ := (congrArg (fun y =>
      (endExt P (natCubicCocycle (k := k) P f hf)).comp y (show 3+3=6 from rfl))
    (natCubic_endExt_eq (k := k) P g hg)).trans
      (cubic_endExt_comp_extMk (k := k) P f hf (g 0 ≫ P.π.f 0)
        (natCubic_augmented_cycle P g hg))
  have h₂ := (congrArg (fun y =>
      (endExt P (natCubicCocycle (k := k) P g hg)).comp y (show 3+3=6 from rfl))
    (natCubic_endExt_eq (k := k) P f hf)).trans
      (cubic_endExt_comp_extMk (k := k) P g hg (f 0 ≫ P.π.f 0)
        (natCubic_augmented_cycle P f hf))
  refine h₁.trans ((extMk_eq_of_map_eq P _ _ _ _ ?_).trans h₂.symm)
  change f 3 ≫ (g 0 ≫ P.π.f 0) = g 3 ≫ (f 0 ≫ P.π.f 0)
  rw [← Category.assoc, hfg, Category.assoc]

end ArExplicit.ResolutionProducts

end

end OAI
