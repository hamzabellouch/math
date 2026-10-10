import OAI.CategoryTheory.ThickClosure.FiniteTower
import OAI.CategoryTheory.ThickClosure.HomologyBridge

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.FreeHomology
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v w c h
variable (R : Type u) [Ring R]

lemma free_of_presentation {ι : Type} [Finite ι] {X : ModuleCat.{u} R}
    (p : LimitPresentation (Discrete ι) X)
    (hf : ∀ i : Discrete ι, Module.Free R (p.diag.obj i)) : Module.Free R X := by
  classical
  let e : X ≅ ModuleCat.of R (∀ i : ι, p.diag.obj ⟨i⟩) :=
    p.isLimit.conePointUniqueUpToIso (limit.isLimit p.diag) ≪≫
      HasLimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ ModuleCat.piIsoPi _
  let (i : ι) : Module.Free R (p.diag.obj ⟨i⟩) := hf ⟨i⟩
  exact Module.Free.of_equiv e.toLinearEquiv.symm

variable [HasDerivedCategory.{v} (ModuleCat.{u} R)]
variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable (F : C ⥤ DerivedCategory (ModuleCat.{u} R)) [F.CommShift ℤ] [F.IsTriangulated]

omit [IsTriangulated C] in
lemma free_layer (T : C)
    (hT : ∀ n : ℤ, Module.Free R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj (F.obj T)))
    (P : C) (hP : HahnWilson.FiniteTower.FreeLayer C T P) :
    ∀ n : ℤ, Module.Free R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj (F.obj P)) := by
  induction hP with
  | of_mem X hX =>
      obtain ⟨Y, a, e, hY⟩ := hX
      have hY := (ObjectProperty.singleton_iff T Y).mp hY
      subst Y
      intro n
      let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
      let e' : H.obj (F.obj X) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (a+n)).obj (F.obj T) := H.mapIso (F.mapIso e ≪≫ (F.commShiftIso a).app T) ≪≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso a n (a+n) rfl).app (F.obj T)
      let := hT (a+n)
      exact Module.Free.of_equiv e'.toLinearEquiv.symm
  | of_isoClosure e _ ih =>
      intro n
      let := ih n
      exact Module.Free.of_equiv
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso (F.mapIso e)).toLinearEquiv
  | of_limitPresentation p _ ih =>
      intro n
      exact free_of_presentation R (p.map (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n))
        (fun i => ih i n)

end HahnWilson.FreeHomology

end

end OAI
