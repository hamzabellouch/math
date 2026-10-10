import OAI.CategoryTheory.ThickClosure.LaurentModules
import OAI.CategoryTheory.ThickClosure.Criterion

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentCriterion
section ModuleCriterion
open CategoryTheory CategoryTheory.Limits
open HahnWilson.LaurentDg HahnWilson.PeriodicDerived HahnWilson.PeriodicDual
universe u w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

abbrev coefficient : LaurentDg.Module R D := LaurentDg.inflateObj (cell R D 0)
abbrev B : LaurentDg.Derived R D := (LaurentDg.localization R D).obj (coefficient R D)

def coefficientIso : B R D ≅ (Q R D).obj (cell R D 0) :=
  (Q R D).mapIso (LaurentDg.counitApp (cell R D 0))

def dualHomologyMap {M N : LaurentDg.Derived R D} (f : M ⟶ N) (n : ℤ) :
    (N ⟶ (B R D)⟦n⟧) → (M ⟶ (B R D)⟦n⟧) := fun a => f ≫ a

end ModuleCriterion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.LaurentDg HahnWilson.PrincipalModules
universe u v w c h
variable (S₀ : Type u) [Ring S₀] [IsDomain S₀]
  [IsPrincipalIdealRing S₀] [IsPrincipalIdealRing S₀ᵐᵒᵖ]
variable (D : ℕ) (hD : 0 < D) (heven : Even D)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} S₀ᵐᵒᵖ)
  (.down (ZMod D))).HasLocalization.{w}]
variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]

include hD heven in

theorem finite_tower_criterion
    (T₀ U₀ : C) (Ψ : C ⥤ LaurentDg.Derived S₀ᵐᵒᵖ D) [Ψ.CommShift ℤ]
    (hΨ : HahnWilson.FiniteTowerCriterion.ExactPerfect S₀ D C Ψ)
    (eT : Ψ.obj T₀ ≅ B S₀ᵐᵒᵖ D)
    (htor : ∀ n : ℤ, IsTorsionModule S₀ᵐᵒᵖ ((derivedHomology n).obj (Ψ.obj U₀)))
    (hnonzero : ∃ n : ℤ, ¬ IsZero ((derivedHomology n).obj (Ψ.obj U₀)))
    (htests : ∀ P, HahnWilson.FiniteTower.Thick C T₀ P → ∀ g : U₀ ⟶ P,
      (∀ n : ℤ, (derivedHomology n).map (Ψ.map g) = 0) →
        ∀ n : ℤ, dualHomologyMap S₀ᵐᵒᵖ D (Ψ.map g) n = 0) :
    ¬ HahnWilson.FiniteTower.Thick C T₀ U₀ := by
  let := HasDerivedCategory.standard (ModuleCat.{u} S₀ᵐᵒᵖ)
  apply HahnWilson.FiniteTowerCriterion.finite_tower_criterion S₀ D hD heven C
    T₀ U₀ Ψ hΨ (eT ≪≫ coefficientIso S₀ᵐᵒᵖ D)
  · intro i
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective i
    exact htor n
  · obtain ⟨n, hn⟩ := hnonzero
    exact ⟨(n : ZMod D), hn⟩
  · intro P hP g hg
    apply (HahnWilson.PeriodicDual.dualGhost_iff S₀ᵐᵒᵖ D (Ψ.map g)).mpr
    intro n a
    let e := (shiftFunctor (LaurentDg.Derived S₀ᵐᵒᵖ D) n).mapIso
      (coefficientIso S₀ᵐᵒᵖ D)
    have ht := htests P hP g (fun m => hg (m : ZMod D)) n
    have ha := congrFun ht (a ≫ e.inv)
    change Ψ.map g ≫ (a ≫ e.inv) = 0 at ha
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, CategoryTheory.Limits.zero_comp] using ha

end HahnWilson.LaurentCriterion

end

end OAI
