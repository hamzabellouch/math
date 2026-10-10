import OAI.Algebra.AuslanderReiten.HomComplex.FullCochainTail
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleFunctor
import OAI.Algebra.AuslanderReiten.Resolutions.ProjectiveResolutionFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]

omit [F.Additive] in
private theorem functor_iso_square {A₀ A₁ B₀ B₁ : ModuleCat.{u} R}
    {U V : ModuleCat.{u} S} (a : A₀ ≅ A₁) (b : B₀ ≅ B₁)
    (e : U ≅ F.obj A₁) (f : V ≅ F.obj B₁) (d : A₁ ⟶ B₁) :
    (e.hom ≫ F.map a.inv) ≫ F.map (a.hom ≫ d ≫ b.inv) =
      (e.hom ≫ F.map d ≫ f.inv) ≫ f.hom ≫ F.map b.inv := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc, a.inv_hom_id, F.map_id, Category.id_comp]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
abbrev functorComplex := (F.mapHomologicalComplex (.up ℤ)).obj K
local notation "FK" => functorComplex F K

def tailFunctorHom :
    nonnegativeTail (chainOfCochain FK) ⟶
      (F.mapHomologicalComplex (.down ℕ)).obj (nonnegativeTail (chainOfCochain K)) where
  f n := (tailTermIso FK n).hom ≫ F.map (tailTermIso K n).inv
  comm' n m hnm := by
    have hnm' : m+1=n := hnm
    subst n
    change ((tailTermIso FK (m+1)).hom ≫ F.map (tailTermIso K (m+1)).inv) ≫
        F.map ((nonnegativeTail (chainOfCochain K)).d (m+1) m) =
      (nonnegativeTail (chainOfCochain FK)).d (m+1) m ≫
        (tailTermIso FK m).hom ≫ F.map (tailTermIso K m).inv
    rw [tailTerm_d K _ _ rfl, tailTerm_d FK _ _ rfl]
    exact functor_iso_square F (tailTermIso K (m+1)) (tailTermIso K m)
      (tailTermIso FK (m+1)) (tailTermIso FK m) (K.d (-((m+1 : ℕ) : ℤ)) (-(m : ℤ)))

theorem tailFunctorHom_cochain (r n : ℕ) (x : Cochain K K (r : ℤ)) :
    cochainTailMap FK FK r (x.map F) n ≫ (tailFunctorHom F K).f n =
      (tailFunctorHom F K).f (r+n) ≫ F.map (cochainTailMap K K r x n) := by
  dsimp only [cochainTailMap, tailFunctorHom]
  exact (functor_iso_square F (tailTermIso K (r+n)) (tailTermIso K n)
    (tailTermIso FK (r+n)) (tailTermIso FK n)
    (x.v (-((r+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega))).symm

end ArExplicit.CompleteComparison

end

end OAI
