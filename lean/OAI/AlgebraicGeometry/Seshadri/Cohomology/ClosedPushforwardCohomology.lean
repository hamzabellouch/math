import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Frames
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ClosedPushforwardExact

namespace OAI


                                                     
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
local instance : HasExt.{1} X.Modules := schemeHasExt
local instance : HasExt.{1} Y.Modules := schemeHasExt
local instance : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf

def cohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{1} (O X) M n →+ Ext.{1} (O Y) ((Scheme.Modules.pushforward f).obj M) n :=
  ((Ext.mk₀ (IdealModule.structureMap f)).precomp _ (zero_add n)).comp
    ((Scheme.Modules.pushforward f).mapExtAddHom (O X) M n)

omit [IsClosedImmersion f] in
lemma globalHom_push (M : X.Modules) (g : O X ⟶ M) :
    globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M)
      (IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) =
    globalHomEquiv X.ringCatSheaf M g := by
  change (g.val.app (op ⊤)) ((f.app ⊤) 1) = (g.val.app (op ⊤)) (1 : Γ(X,⊤))
  rw [map_one]
  rfl

lemma cohomologyMap_zero_bijective (M : X.Modules) :
    Function.Bijective (cohomologyMap f M 0) := by
  have hhom : Function.Bijective (fun g : O X ⟶ M =>
      IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
    constructor
    · intro a b h
      apply (globalHomEquiv X.ringCatSheaf M).injective
      exact (globalHom_push f M a).symm.trans
        ((congrArg (globalHomEquiv Y.ringCatSheaf _) h).trans (globalHom_push f M b))
    · intro b
      obtain ⟨a,ha⟩ := (globalHomEquiv X.ringCatSheaf M).surjective
        (globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M) b)
      refine ⟨a,?_⟩
      apply (globalHomEquiv Y.ringCatSheaf _).injective
      exact (globalHom_push f M a).trans ha
  have he : (cohomologyMap f M 0) ∘ Ext.mk₀ = Ext.mk₀ ∘
      (fun g : O X ⟶ M => IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
    funext g
    change (Ext.mk₀ (IdealModule.structureMap f)).comp
      ((Ext.mk₀ g).mapExactFunctor (Scheme.Modules.pushforward f)) (zero_add 0) = _
    rw [Ext.mapExactFunctor_mk₀]
    exact Ext.mk₀_comp_mk₀ (IdealModule.structureMap f) ((Scheme.Modules.pushforward f).map g)
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).mp (by
    rw [he]
    exact (Ext.mk₀_bijective _ _).comp hhom)

omit [IsClosedImmersion f] in
lemma pushforward_flasque (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf.{0} Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) := by
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) f.base

lemma cohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (a : Ext (O X) M n) (b : Ext M N m) (h : n+m=k) :
    cohomologyMap f N k (a.comp b h) =
      (cohomologyMap f M n a).comp
        (b.mapExactFunctor (Scheme.Modules.pushforward f)) h := by
  change (Ext.mk₀ (IdealModule.structureMap f)).comp
    ((a.comp b h).mapExactFunctor _) (zero_add _) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem cohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (cohomologyMap f M n) := by
  induction n generalizing M with
  | zero => exact cohomologyMap_zero_bijective f M
  | succ n ih =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let F := Scheme.Modules.pushforward f
    let : Injective S.X₂ := I.injective
    let : TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj S.X₂) :=
      @ModuleFlasque.injective_isFlasque _ X.ringCatSheaf S.X₂ I.injective
    let hfl : TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf.{0} Y.ringCatSheaf).obj ((S.map F).X₂)) :=
      pushforward_flasque f S.X₂
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (cohomologyMap f S.X₂ n) (cohomologyMap f S.X₃ n) (cohomologyMap f S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (O X) hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (O Y) (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _) ?_ ?_
    · ext a
      change (cohomologyMap f S.X₂ n a).comp (Ext.mk₀ (F.map S.g)) (add_zero n) =
        cohomologyMap f S.X₃ n (a.comp (Ext.mk₀ S.g) (add_zero n))
      rw [cohomologyMap_comp, Ext.mapExactFunctor_mk₀]
    · ext a
      change (cohomologyMap f S.X₃ n a).comp (hS.map F).extClass rfl =
        cohomologyMap f S.X₁ (n+1) (a.comp hS.extClass rfl)
      rw [cohomologyMap_comp, Ext.mapExactFunctor_extClass]
    · intro a
      exact Ext.covariant_sequence_exact₁ _ hS a (Ext.eq_zero_of_injective _) rfl
    · intro a
      exact Ext.covariant_sequence_exact₁ _ (hS.map F) a
        (@flasque_ext_zero.{0} (Y : TopCat) Y.ringCatSheaf n _ hfl _) rfl

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
