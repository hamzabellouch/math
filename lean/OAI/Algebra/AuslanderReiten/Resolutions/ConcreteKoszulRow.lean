import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicAction
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverStep
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedConnectingCoordinates
import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedBoundaryComponents
import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductReindex
import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicStepAction
import OAI.Algebra.AuslanderReiten.Coordinates.GradedRowCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q

theorem simpleSkeletonRow_fullHom (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedSingletonResolution q 0)⟦a⟧) :
    evaluatedBaseFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.connecting k (simpleSkeletonTriangle q 0)
        (evaluatedSimpleObject q) a v) =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=(a+1)-((0:ℕ):ℤ))
      (fullHomProduct (evaluatedSingletonFullHomEquiv q 0 a v).1 (firstCoverClass q) +
       fullHomProduct (evaluatedSingletonFullHomEquiv q 0 a v).2 (secondCoverClass q)) := by
  have hr := connectingRow (k := k) (simpleSkeletonTriangle q 0)
    (evaluatedSimpleObject q) (evaluatedBaseResolution q 2) (evaluatedBaseResolution q 3)
    a v
    ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q 0)))
    ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q 0)))
    (evaluatedBaseStepIso q 2).hom
    (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ 0)
    (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ 0)
    (simpleSkeletonConnecting_components q 0)
  have h₁ := evaluatedFirstCokernel_step_action q 0 a
    (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q 0)))⟦a⟧')
  have h₂ := evaluatedSecondCokernel_step_action q 0 a
    (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q 0)))⟦a⟧')
  exact additiveRowCoordinates (evaluatedBaseFullHomEquiv q 0 (a+1)).toAddMonoidHom
    (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=(a+1)-((0:ℕ):ℤ))).toAddMonoidHom
    (fun z => fullHomProduct z (firstCoverClass q))
    (fun z => fullHomProduct z (secondCoverClass q)) hr h₁ h₂
    (evaluatedSingletonFullHomEquiv_fst q 0 a v)
    (evaluatedSingletonFullHomEquiv_snd q 0 a v)

end ArExplicit.T

end

end OAI
