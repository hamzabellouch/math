import OAI.CategoryTheory.ThickClosure.CyclicShift
import OAI.CategoryTheory.ThickClosure.DerivedHom

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicDual
section DualModules
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
universe u w
variable (R : Type u) [Ring R] (D : ℕ)

def cell (i : ZMod D) : PeriodicComplex R D :=
  diagonalComplex (fun j => ModuleCat.of R (PLift (j = i) → R))

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

def DualGhost {P P' : PeriodicDerived R D} (f : P ⟶ P') : Prop :=
  ∀ i (a : P' ⟶ (Q R D).obj (cell R D i)), f ≫ a = 0

end DualModules

section ChosenBases
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
universe u w
variable (R : Type u) [Ring R] (D : ℕ) [NeZero D]
variable (V : ZMod D → ModuleCat.{u} R)
variable [∀ i, Module.Free R (V i)] [∀ i, Module.Finite R (V i)]

abbrev BasisIndex := Σ i : ZMod D, Module.Free.ChooseBasisIndex R (V i)

noncomputable def coordinate (t : BasisIndex R D V) : diagonalComplex V ⟶ cell R D t.1 where
  f j := ModuleCat.ofHom
    { toFun := fun x h => (Module.Free.chooseBasis R (V t.1)).equivFun (h.down ▸ x) t.2
      map_add' := by intros; ext h; obtain ⟨h⟩ := h; subst j; simp
      map_smul' := by intros; ext h; obtain ⟨h⟩ := h; subst j; simp }
  comm' i j hij := by
    change _ ≫ (diagonalComplex (fun k => ModuleCat.of R (PLift (k = t.1) → R))).d i j =
      (diagonalComplex V).d i j ≫ _
    simp [diagonalComplex, ChainComplex.of.d]

noncomputable def coordinateFan : Fan (fun t : BasisIndex R D V => cell R D t.1) :=
  Fan.mk (diagonalComplex V) (coordinate R D V)

noncomputable def coordinateLift (s : Fan (fun t : BasisIndex R D V => cell R D t.1)) :
    s.pt ⟶ diagonalComplex V where
  f j := ModuleCat.ofHom ((Module.Free.chooseBasis R (V j)).equivFun.symm.toLinearMap.comp
      (LinearMap.pi (fun b => (LinearMap.proj (PLift.up rfl)).comp ((s.π.app ⟨⟨j,b⟩⟩).f j).hom)))
  comm' i j hij := by
    change _ ≫ (diagonalComplex V).d i j = s.pt.d i j ≫ _
    rw [diagonalComplex_d, CategoryTheory.Limits.comp_zero]
    apply ModuleCat.hom_ext
    ext x
    change 0 = (Module.Free.chooseBasis R (V j)).equivFun.symm
      (fun b => (s.π.app ⟨⟨j,b⟩⟩).f j (s.pt.d i j x) (PLift.up rfl))
    apply (Module.Free.chooseBasis R (V j)).equivFun.injective
    rw [map_zero, LinearEquiv.apply_symm_apply]
    funext b
    have h := congrArg (fun (a : s.pt.X i ⟶ (cell R D j).X j) => a x (PLift.up rfl))
      ((s.π.app ⟨⟨j,b⟩⟩).comm i j)
    change ((s.π.app ⟨⟨j,b⟩⟩).f i ≫ (diagonalComplex _).d i j) x _ = _ at h
    erw [diagonalComplex_d, CategoryTheory.Limits.comp_zero] at h
    exact h

noncomputable def coordinateFanIsLimit : IsLimit (coordinateFan R D V) := by
  classical
  refine Fan.IsLimit.mk _ (coordinateLift R D V) ?_ ?_
  · intro s t
    apply Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    obtain ⟨i,b⟩ := t
    obtain ⟨h⟩ := h
    dsimp at h
    subst j
    change (Module.Free.chooseBasis R (V i)).equivFun
      ((Module.Free.chooseBasis R (V i)).equivFun.symm _) b = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · intro s m hm
    apply Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Module.Free.chooseBasis R (V j)).equivFun.injective
    change (Module.Free.chooseBasis R (V j)).equivFun (m.f j x) =
      (Module.Free.chooseBasis R (V j)).equivFun
        ((Module.Free.chooseBasis R (V j)).equivFun.symm _)
    rw [LinearEquiv.apply_symm_apply]
    funext b
    exact congrArg (fun (a : s.pt ⟶ cell R D j) => a.f j x (PLift.up rfl)) (hm ⟨j,b⟩)

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

 theorem dualGhost_free_zero_inst
    {P : PeriodicDerived R D} (f : P ⟶ (Q R D).obj (diagonalComplex V))
    (hf : DualGhost R D f) : f = 0 := by
  have hc := isLimitOfPreserves (Q R D) (coordinateFanIsLimit R D V)
  apply hc.hom_ext
  intro j
  change f ≫ (Q R D).map (coordinate R D V j.as) = 0 ≫ _
  rw [CategoryTheory.Limits.zero_comp]
  exact hf j.as.1 _

end ChosenBases

section DerivedDual
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
universe u w
variable (R : Type u) [Ring R] (D : ℕ) [NeZero D]
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
theorem dualGhost_free_zero (V : ZMod D → ModuleCat.{u} R)
    (hV : ∀ i, Module.Free R (V i) ∧ Module.Finite R (V i))
    {P : PeriodicDerived R D} (f : P ⟶ (Q R D).obj (diagonalComplex V))
    (hf : DualGhost R D f) : f = 0 := by
  let (i : ZMod D) := (hV i).1
  let (i : ZMod D) := (hV i).2
  exact dualGhost_free_zero_inst R D V f hf

omit [NeZero D] in
lemma DualGhost.comp_right {P P' P'' : PeriodicDerived R D}
    {f : P ⟶ P'} (hf : DualGhost R D f) (g : P' ⟶ P'') : DualGhost R D (f ≫ g) := by
  intro i a
  rw [Category.assoc]
  exact hf i (g ≫ a)

end DerivedDual

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived HahnWilson.CyclicShift
universe u w
variable (R : Type u) [Ring R] (D : ℕ)

noncomputable def cellShiftIso (n : ℤ) :
    ((cell R D 0)⟦n⟧) ≅ cell R D (n : ZMod D) := by
  refine Hom.isoOfComponents (fun i => ?_) ?_
  · exact (LinearEquiv.piCongrLeft R (fun _ : PLift (i = (n : ZMod D)) => R)
      (Equiv.plift.trans ((Equiv.ofIff sub_eq_zero).trans Equiv.plift.symm))).toModuleIso
  · intro i j hij
    change _ ≫ (cell R D (n : ZMod D)).d i j =
      ((cyclicShift R D n).obj (cell R D 0)).d i j ≫ _
    simp [cell, cyclicShift, diagonalComplex, ChainComplex.of.d]

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

lemma dualGhost_iff {P P' : PeriodicDerived R D} (f : P ⟶ P') :
    DualGhost R D f ↔
      ∀ n : ℤ, ∀ a : P' ⟶ ((Q R D).obj (cell R D 0))⟦n⟧, f ≫ a = 0 := by
  constructor
  · intro h n a
    let e := ((Q R D).commShiftIso n).symm.app (cell R D 0) ≪≫
      (Q R D).mapIso (cellShiftIso R D n)
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, CategoryTheory.Limits.zero_comp] using h (n : ZMod D) (a ≫ e.hom)
  · intro h i a
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective i
    subst i
    let e := ((Q R D).commShiftIso n).symm.app (cell R D 0) ≪≫
      (Q R D).mapIso (cellShiftIso R D n)
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, CategoryTheory.Limits.zero_comp] using h n (a ≫ e.inv)

end HahnWilson.PeriodicDual

end

end OAI
