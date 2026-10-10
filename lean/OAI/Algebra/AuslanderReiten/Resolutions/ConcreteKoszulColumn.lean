import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicAction
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverStep
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedAdjacentComponents
import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedBoundaryComponents
import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductReindex
import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicStepAction

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

private theorem columnNeg {M : Type u} [AddCommGroup M] [Module k M] (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]

theorem simpleTopColumn_fst (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q 4)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v))).1 =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2)
      (fullHomProduct (evaluatedBaseFullHomEquiv q 4 a v) (secondCoverClass q)) := by
  erw [evaluatedSingletonFullHomEquiv_fst, TriangleGradedSequence.second_eq_shift,
    TriangleGradedSequence.connecting_eq_product, Category.assoc, ← Functor.map_comp,
    ← shiftedComp_post, simpleTopConnecting_fst, shiftedComp_post,
    evaluatedSecondCokernel_step_action]

theorem simpleTopColumn_snd_unsigned (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q 4)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v))).2 =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2)
      (fullHomProduct (evaluatedBaseFullHomEquiv q 4 a v) (firstCoverClass q)) := by
  erw [evaluatedSingletonFullHomEquiv_snd, TriangleGradedSequence.second_eq_shift,
    TriangleGradedSequence.connecting_eq_product, Category.assoc, ← Functor.map_comp,
    ← shiftedComp_post, simpleTopConnecting_snd, shiftedComp_post,
    evaluatedFirstCokernel_step_action]

theorem simpleTopColumn_snd (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q 4)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v))).2 =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2)
      (-(fullHomProduct (evaluatedBaseFullHomEquiv q 4 a v) (firstCoverClass q))) := by
  have h := simpleTopColumn_snd_unsigned q a v
  exact h.trans (congrArg
    (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2))
      (columnNeg (k := k) _).symm)

end ArExplicit.T

end

end OAI
