import OAI.CategoryTheory.ThickClosure.PerfectModules

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.SourceCriterion
section SourceData
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HahnWilson.LaurentDg HahnWilson.PeriodicDerived HahnWilson.PeriodicDual
universe u c h

@[instance_reducible] noncomputable def chosenLocalization (R : Type u) [Ring R] (D : ℕ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{u+1} :=
  MorphismProperty.HasLocalization.standard _
attribute [local instance] chosenLocalization

abbrev DgDerived (R : Type u) [Ring R] (D : ℕ) := LaurentDg.Derived R D

abbrev Perf (R : Type u) [Ring R] (D : ℕ) :=
  ObjectProperty.FullSubcategory (IsPerfect R D)

abbrev inclusion (R : Type u) [Ring R] (D : ℕ) : Perf R D ⥤ DgDerived R D :=
  ObjectProperty.ι (IsPerfect R D)

lemma coefficient_perfect (R : Type u) [Ring R] (D : ℕ) :
    IsPerfect R D (HahnWilson.LaurentCriterion.B R D) := by
  classical
  refine ⟨cell R D 0, FiniteCell.free ⟨?_, ?_⟩,
    ⟨Retract.ofIso (HahnWilson.LaurentCriterion.coefficientIso R D)⟩⟩
  · exact HahnWilson.PeriodicSplitting.diagonalComplex_d _
  · intro i
    change Module.Free R (PLift (i = 0) → R) ∧ Module.Finite R (PLift (i = 0) → R)
    exact ⟨inferInstance, inferInstance⟩

noncomputable def B₀ (R : Type u) [Ring R] (D : ℕ) : Perf R D :=
  ⟨HahnWilson.LaurentCriterion.B R D, coefficient_perfect R D⟩

abbrev H (R : Type u) [Ring R] (D : ℕ) (n : ℤ) : Perf R D ⥤ ModuleCat.{u} R :=
  inclusion R D ⋙ LaurentDg.derivedHomology n

def HdualMap (R : Type u) [Ring R] (D : ℕ)
    {M N : Perf R D} (f : M ⟶ N) (n : ℤ) :=
  HahnWilson.LaurentCriterion.dualHomologyMap R D ((inclusion R D).map f) (-n)

variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]

def Exact (R : Type u) [Ring R] (D : ℕ) (Ψ : C ⥤ Perf R D)
    [(Ψ ⋙ inclusion R D).CommShift ℤ] : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    (Ψ ⋙ inclusion R D).mapTriangle.obj T ∈ HahnWilson.CyclicTriangle.distinguished R D

end SourceData
open CategoryTheory CategoryTheory.Limits
open HahnWilson.PrincipalModules
universe u c h
attribute [local instance] chosenLocalization
variable (S₀ : Type u) [Ring S₀] [IsDomain S₀]
  [IsPrincipalIdealRing S₀] [IsPrincipalIdealRing S₀ᵐᵒᵖ]
variable (D₀ : ℕ) (hD₀ : 0 < D₀) (heven : Even D₀)
variable (C : Type c) [Category.{h} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]
include hD₀ heven in

theorem finite_tower_criterion (T₀ U₀ : C) (Ψ : C ⥤ Perf S₀ᵐᵒᵖ D₀)
    [(Ψ ⋙ inclusion S₀ᵐᵒᵖ D₀).CommShift ℤ]
    (hΨ : Exact C S₀ᵐᵒᵖ D₀ Ψ) (eT : Ψ.obj T₀ ≅ B₀ S₀ᵐᵒᵖ D₀)
    (htor : ∀ n : ℤ, IsTorsionModule S₀ᵐᵒᵖ ((H S₀ᵐᵒᵖ D₀ n).obj (Ψ.obj U₀)))
    (hnonzero : ∃ n : ℤ, ¬ IsZero ((H S₀ᵐᵒᵖ D₀ n).obj (Ψ.obj U₀)))
    (htests : ∀ P, HahnWilson.FiniteTower.Thick C T₀ P → ∀ g : U₀ ⟶ P,
      (∀ n : ℤ, (H S₀ᵐᵒᵖ D₀ n).map (Ψ.map g) = 0) →
        ∀ n : ℤ, HdualMap S₀ᵐᵒᵖ D₀ (Ψ.map g) n = 0) :
    ¬ HahnWilson.FiniteTower.Thick C T₀ U₀ := by
  apply HahnWilson.LaurentCriterion.finite_tower_criterion S₀ D₀ hD₀ heven C
    T₀ U₀ (Ψ ⋙ inclusion S₀ᵐᵒᵖ D₀)
  · exact ⟨fun X => (Ψ.obj X).property, hΨ⟩
  · exact (inclusion S₀ᵐᵒᵖ D₀).mapIso eT
  · exact htor
  · exact hnonzero
  · intro P hP g hg n
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, -m = n := ⟨-n, Int.neg_neg n⟩
    exact htests P hP g hg m
end HahnWilson.SourceCriterion

end

end OAI
