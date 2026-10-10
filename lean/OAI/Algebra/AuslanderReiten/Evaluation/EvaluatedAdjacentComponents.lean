import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedTopConnecting

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
private theorem charTwoNeg (k : Type u) [Field k] [CharP k 2]
    {M : Type*} [AddCommGroup M] [Module k M] (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem evaluatedAdjacentMap_fst (n : ℕ) :
    (evaluatedSingletonFst q n).comp (evaluatedAdjacentMap q n) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.secondCokernelMap D₀ (n+2)) := by
  have h := evaluatedColumn_fst q n
  refine h.trans ?_
  apply LinearMap.ext
  intro z
  exact charTwoNeg k _

theorem evaluatedAdjacentMap_snd (n : ℕ) :
    (evaluatedSingletonSnd q n).comp (evaluatedAdjacentMap q n) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.firstCokernelMap D₀ (n+2)) := evaluatedColumn_snd q n

theorem evaluatedAdjacentHom_fst (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)) ≫
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) =
    TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ (n+2) := by
  rw [← FiniteLeftModule.resolutionMap_comp, evaluatedAdjacentMap_fst]
  rfl

theorem evaluatedAdjacentHom_snd (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)) ≫
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) =
    TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ (n+2) := by
  rw [← FiniteLeftModule.resolutionMap_comp, evaluatedAdjacentMap_snd]
  rfl

theorem simpleTopConnecting_fst (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫
      ((simpleSkeletonTriangle q n).mor₂ ≫
        (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)))⟦(1 : ℤ)⟧' =
    (evaluatedBaseStepIso q (n+4)).hom ≫
      (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ (n+2))⟦(1 : ℤ)⟧' := by
  erw [Functor.map_comp, ← Category.assoc, simpleTopConnecting_adjacent,
    Category.assoc, ← Functor.map_comp, evaluatedAdjacentHom_fst]
  rfl

theorem simpleTopConnecting_snd (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫
      ((simpleSkeletonTriangle q n).mor₂ ≫
        (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)))⟦(1 : ℤ)⟧' =
    (evaluatedBaseStepIso q (n+4)).hom ≫
      (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ (n+2))⟦(1 : ℤ)⟧' := by
  erw [Functor.map_comp, ← Category.assoc, simpleTopConnecting_adjacent,
    Category.assoc, ← Functor.map_comp, evaluatedAdjacentHom_snd]
  rfl

end ArExplicit.T

end

end OAI
