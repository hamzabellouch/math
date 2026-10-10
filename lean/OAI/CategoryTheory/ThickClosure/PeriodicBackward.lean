import OAI.CategoryTheory.ThickClosure.FreeHomology
import OAI.CategoryTheory.ThickClosure.BackwardStep
import OAI.CategoryTheory.ThickClosure.PeriodicDual

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicBackward
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.PrincipalModules HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
open HahnWilson.PeriodicDual HahnWilson.Unroll HahnWilson.GradedSplit
universe u v w
variable (R : Type u) [Ring R] [IsDomain R]
  [IsPrincipalIdealRing R] [IsPrincipalIdealRing Rᵐᵒᵖ]
  (D : ℕ) (hD : 0 < D) (heven : Even D)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]

include hD heven in

theorem step (T : Triangle (PeriodicDerived R D))
    (hT : T ∈ HahnWilson.CyclicTriangle.distinguished R D)
    (hP : IsPerfect R D T.obj₃)
    {Y : PeriodicDerived R D} (g : Y ⟶ T.obj₂)
    (hY : ∀ i, IsTorsionModule R ((homology R D i).obj Y))
    (hF : ∀ n : ℤ, Module.Free R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((derivedFunctor R D).obj T.obj₁)))
    (hg : ∀ i, (homology R D i).map (g ≫ T.mor₂) = 0)
    (hd : DualGhost R D (g ≫ T.mor₂)) :
    ∀ i, (homology R D i).map g = 0 := by
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  obtain ⟨V,L,hV,hL,_,⟨eP⟩⟩ := perfect_splitting (R := R) (D := D) hD heven T.obj₃ hP
  let A := derivedFunctor R D
  let e := A.mapIso eP ≪≫ (derivedFactors R D).app (dgProd R D V L)
  let l : (F₀ R D).obj (dg R D L) ⟶ A.obj T.obj₃ :=
    (F₀ R D).map (iL R D V L) ≫ e.inv
  let v : A.obj T.obj₃ ⟶ (F₀ R D).obj (dg R D V) :=
    e.hom ≫ (F₀ R D).map (pV R D V L)
  let r : A.obj T.obj₃ ⟶ (F₀ R D).obj (dg R D L) :=
    e.hom ≫ (F₀ R D).map (pL R D V L)
  have hsplit : Triangle.mk l v 0 ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) := by
    apply isomorphic_distinguished _ (splitTriangle R D V L)
    refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
    · change l ≫ e.hom = 𝟙 _ ≫ (F₀ R D).map (iL R D V L)
      simp [l]
    · change v ≫ 𝟙 _ = e.hom ≫ (F₀ R D).map (pV R D V L)
      simp [v]
    · change (0 : (F₀ R D).obj (dg R D V) ⟶ ((F₀ R D).obj (dg R D L))⟦(1:ℤ)⟧) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1:ℤ)).map (𝟙 ((F₀ R D).obj (dg R D L))) =
          𝟙 _ ≫ 0
      simp
  have hlr : l ≫ r = 𝟙 _ := by
    simp only [l, r, Category.assoc, e.inv_hom_id_assoc, ← Functor.map_comp, iL_pL]
    exact (F₀ R D).map_id _
  have hfzero : (g ≫ T.mor₂) ≫ (eP.hom ≫ (Q R D).map (pV R D V L)) = 0 :=
    dualGhost_free_zero R D V hV _ (DualGhost.comp_right R D hd _)
  have hnat := (derivedFactors R D).hom.naturality (pV R D V L)
  change A.map ((Q R D).map (pV R D V L)) ≫ (derivedFactors R D).hom.app (dg R D V) =
    (derivedFactors R D).hom.app (dgProd R D V L) ≫ (F₀ R D).map (pV R D V L) at hnat
  have hgv : A.map g ≫ A.map T.mor₂ ≫ v = 0 := by
    calc
      _ = A.map ((g ≫ T.mor₂) ≫ (eP.hom ≫ (Q R D).map (pV R D V L))) ≫
          (derivedFactors R D).hom.app (dg R D V) := by
            simp only [v, e, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
              Category.assoc, hnat]
            rfl
      _ = 0 := by rw [hfzero, A.map_zero, CategoryTheory.Limits.zero_comp]
  apply (HahnWilson.HomologyBridge.all_zero_iff R D g).mp
  intro n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let := hF n
  exact HahnWilson.BackwardStep.homology_backward_step H
    (A.map T.mor₁) (A.map T.mor₂)
    (A.map T.mor₃ ≫ (A.commShiftIso (1:ℤ)).hom.app T.obj₁)
    (HahnWilson.CyclicTriangle.map_distinguished R D T hT)
    l v 0 hsplit r hlr
    (HahnWilson.HomologyBridge.torsion R D Y hY n)
    (HahnWilson.HomologyBridge.torsion_shift_diagonal R D L hL (-1) n)
    (A.map g) (by
      simpa only [Functor.map_comp] using
        (HahnWilson.HomologyBridge.zero_iff R D (g ≫ T.mor₂) n).mpr (hg _)) hgv

end HahnWilson.PeriodicBackward

end

end OAI
