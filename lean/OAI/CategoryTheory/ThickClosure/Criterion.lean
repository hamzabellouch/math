import OAI.CategoryTheory.ThickClosure.PeriodicBackward

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.FiniteTowerCriterion
section ModuleCriterion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.PrincipalModules HahnWilson.PeriodicDerived HahnWilson.PeriodicDual
universe u v w c h
variable (S₀ : Type u) [Ring S₀] [IsDomain S₀]
  [IsPrincipalIdealRing S₀] [IsPrincipalIdealRing S₀ᵐᵒᵖ]
variable (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} S₀ᵐᵒᵖ)
  (.down (ZMod D))).HasLocalization.{w}]
variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]

def ExactPerfect (Ψ : C ⥤ PeriodicDerived S₀ᵐᵒᵖ D) [Ψ.CommShift ℤ] : Prop :=
  (∀ X, IsPerfect S₀ᵐᵒᵖ D (Ψ.obj X)) ∧
  ∀ T : Triangle C, T ∈ distTriang C →
    Ψ.mapTriangle.obj T ∈ HahnWilson.CyclicTriangle.distinguished S₀ᵐᵒᵖ D

end ModuleCriterion

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.PrincipalModules HahnWilson.PeriodicDerived HahnWilson.PeriodicDual
universe u v w c h
variable (S₀ : Type u) [Ring S₀] [IsDomain S₀]
  [IsPrincipalIdealRing S₀] [IsPrincipalIdealRing S₀ᵐᵒᵖ]
variable (D : ℕ) (hD : 0 < D) (heven : Even D)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} S₀ᵐᵒᵖ)
  (.down (ZMod D))).HasLocalization.{w}]
variable [HasDerivedCategory.{v} (ModuleCat.{u} S₀ᵐᵒᵖ)]
variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]

include hD heven in

theorem finite_tower_criterion
    (T₀ U₀ : C) (Ψ : C ⥤ PeriodicDerived S₀ᵐᵒᵖ D) [Ψ.CommShift ℤ]
    (hΨ : ExactPerfect S₀ D C Ψ)
    (eT : Ψ.obj T₀ ≅ (Q S₀ᵐᵒᵖ D).obj (cell S₀ᵐᵒᵖ D 0))
    (htor : ∀ i, IsTorsionModule S₀ᵐᵒᵖ ((homology S₀ᵐᵒᵖ D i).obj (Ψ.obj U₀)))
    (hnonzero : ∃ i, ¬ IsZero ((homology S₀ᵐᵒᵖ D i).obj (Ψ.obj U₀)))
    (htests : ∀ P, HahnWilson.FiniteTower.Thick C T₀ P → ∀ g : U₀ ⟶ P,
      (∀ i, (homology S₀ᵐᵒᵖ D i).map (Ψ.map g) = 0) →
        DualGhost S₀ᵐᵒᵖ D (Ψ.map g)) :
    ¬ HahnWilson.FiniteTower.Thick C T₀ U₀ := by
  classical
  let R := S₀ᵐᵒᵖ
  let : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective (RingEquiv.opOp S₀) (RingEquiv.opOp S₀).surjective
  let A := HahnWilson.Unroll.derivedFunctor R D
  let F := Ψ ⋙ A
  let : F.IsTriangulated := ⟨fun T hT => by
    apply isomorphic_distinguished _
      (HahnWilson.CyclicTriangle.map_distinguished R D (Ψ.mapTriangle.obj T) (hΨ.2 T hT))
    exact (Functor.mapTriangleCompIso Ψ A).app T⟩
  have hTfree (n : ℤ) : Module.Free R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj (F.obj T₀)) := by
    let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj (F.obj T₀) ≅
        ModuleCat.of R (PLift (-(n : ZMod D) = 0) → R) :=
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso (A.mapIso eT) ≪≫
        HahnWilson.GradedSplit.derivedDiagonalHomologyIso R D
          (fun i => ModuleCat.of R (PLift (i = 0) → R)) n
    exact Module.Free.of_equiv e.toLinearEquiv.symm
  have hghost (P : C) (hP : HahnWilson.FiniteTower.Tower C T₀ P) :
      ∀ g : U₀ ⟶ P, ∀ i, (homology R D i).map (Ψ.map g) = 0 := by
    induction hP with
    | @zero P hz =>
        intro g
        apply (HahnWilson.HomologyBridge.all_zero_iff R D (Ψ.map g)).mp
        intro n
        exact ((F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map_isZero hz).eq_of_tgt _ _
    | step tr htr hf ht ih =>
        intro g
        have hg₂ : ∀ i, (homology R D i).map (Ψ.map g ≫ Ψ.map tr.mor₂) = 0 := by
          simpa only [Functor.map_comp] using ih (g ≫ tr.mor₂)
        have hd₂ : DualGhost R D (Ψ.map g ≫ Ψ.map tr.mor₂) := by
          simpa only [Functor.map_comp] using
            htests tr.obj₃ (HahnWilson.FiniteTower.tower_thick C T₀ _ ht)
              (g ≫ tr.mor₂) (ih (g ≫ tr.mor₂))
        exact HahnWilson.PeriodicBackward.step R D hD heven (Ψ.mapTriangle.obj tr)
          (hΨ.2 tr htr) (hΨ.1 _) (Ψ.map g) htor
          (HahnWilson.FreeHomology.free_layer R C F T₀ hTfree tr.obj₁ hf) hg₂ hd₂
  intro hU
  obtain ⟨P,hP,⟨r⟩⟩ := HahnWilson.FiniteTower.tower_normal_form C T₀ U₀ hU
  obtain ⟨i,hi⟩ := hnonzero
  apply hi
  apply (IsZero.iff_id_eq_zero _).mpr
  have hr := congrArg (fun f => (homology R D i).map (Ψ.map f)) r.retract
  have hid : (homology R D i).map (Ψ.map (𝟙 U₀)) = 𝟙 _ :=
    (congrArg (fun f => (homology R D i).map f) (Ψ.map_id U₀)).trans
      ((homology R D i).map_id _)
  apply hid.symm.trans
  simpa only [Functor.map_comp, hghost P hP r.i i,
    CategoryTheory.Limits.zero_comp] using hr.symm
end HahnWilson.FiniteTowerCriterion

end

end OAI
