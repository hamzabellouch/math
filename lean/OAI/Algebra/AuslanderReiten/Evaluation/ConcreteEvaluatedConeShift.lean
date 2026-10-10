import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCosyzygyShift
import OAI.Algebra.AuslanderReiten.Cones.TwoConeStableRepresentative
import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "τe₀" => AEnvelopingFrobeniusTrace k q

theorem coneCokernel_right_projective (n : ℕ) : Module.Projective R₀ᵐᵒᵖ
    (EnvelopingBimodule k R₀ (TwoCone.cokernelModule D₀ hf₀ n).carrier) := by
  let j := tensorRightInclusion k R₀ R₀ᵐᵒᵖ
  have hp (m : ℕ) : Module.Projective R₀ᵐᵒᵖ (TwoCone.BaseCokernel ((D₀).restrict j) m) := by
    let := baseTail_right_projective q m
    exact Module.Projective.of_equiv
      ((EnvelopingBimodule.rightEquiv (TwoCone.baseCokernelModule D₀ hf₀ m).carrier).trans
        (TwoCone.baseCokernelRestrictionEquiv j D₀ m))
  let := TwoCone.cokernel_projective ((D₀).restrict j)
    (TwoCone.restricted_exact j D₀ (bimodule_exact q)) hp n
  exact Module.Projective.of_equiv
    ((EnvelopingBimodule.rightEquiv (TwoCone.cokernelModule D₀ hf₀ n).carrier).trans
      (TwoCone.cokernelRestrictionEquiv j D₀ n)).symm

theorem firstTailCosyzygies_right_projective (n : ℕ) : Module.Projective R₀ᵐᵒᵖ
    (EnvelopingBimodule k R₀ ((firstTailModule q).canonicalCosyzygies n).carrier) := by
  let := firstTailModule_right_finite q
  let := firstTailModule_right_projective q
  let := tensorRightRegular_finite k R₀ R₀ᵐᵒᵖ
  let := tensorRightRegular_projective k R₀ R₀ᵐᵒᵖ
  obtain ⟨hfin, hproj⟩ := (firstTailModule q).canonicalCosyzygies_side
    (tensorRightInclusion k R₀ R₀ᵐᵒᵖ) τe₀ n
  let := hproj
  infer_instance

abbrev evaluatedConeModule (n : ℕ) :=
  FiniteLeftModule.evaluated X₀ (TwoCone.cokernelModule D₀ hf₀ n)

def evaluatedConeSuccessorIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((evaluatedConeModule q n).completeCochain τ₀) ≅
      ((HomotopyCategory.quotient _ _).obj
        ((evaluatedConeModule q (n+1)).completeCochain τ₀))⟦(1 : ℤ)⟧ := by
  letI := coneCokernel_right_projective q n
  letI : Module.Projective (R₀ ⊗[k] R₀ᵐᵒᵖ) (TwoCone.term D₀ n) :=
    TwoCone.term_projective D₀ (bimodule_term_projective q) n
  exact FiniteLeftModule.evaluationSuccessorIso X₀
    (M := TwoCone.cokernelModule D₀ hf₀ (n+1))
    (N := TwoCone.coneTermModule D₀ hf₀ n) (P := TwoCone.cokernelModule D₀ hf₀ n)
    (TwoCone.baseStepInclusion (TwoCone.coneTailData D₀) (TwoCone.d_exact D₀ (bimodule_exact q)) n)
    (LinearMap.range (TwoCone.d D₀ n)).mkQ
    (TwoCone.baseStepInclusion_injective (TwoCone.coneTailData D₀)
      (TwoCone.d_exact D₀ (bimodule_exact q)) n)
    ((LinearMap.range (TwoCone.d D₀ n)).mkQ_surjective)
    (TwoCone.baseStep_exact (TwoCone.coneTailData D₀) (TwoCone.d_exact D₀ (bimodule_exact q)) n) τ₀

def evaluatedBranchTargetShiftIso :
    (HomotopyCategory.quotient _ _).obj
      ((FiniteLeftModule.evaluated X₀ (fiberTarget q)).completeCochain τ₀) ≅
    ((HomotopyCategory.quotient _ _).obj
      ((evaluatedConeModule q 0).completeCochain τ₀))⟦(3 : ℤ)⟧ :=
  FiniteLeftModule.evaluatedCanonicalCosyzygiesShiftIso X₀ τe₀ τ₀ (firstTailModule q)
    (firstTailCosyzygies_right_projective q) 4 ≪≫
    ((CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R₀) (ComplexShape.up ℤ)) 3).mapIso
      (evaluatedConeSuccessorIso q 0) ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R₀) (ComplexShape.up ℤ))
        1 3 4 (by decide)).symm.app _).symm

end ArExplicit.T

end

end OAI
