import OAI.Combinatorics.ContingencyTables.Rooted.RootedIntegerEvaluation
import OAI.Combinatorics.ContingencyTables.Rooted.ForestPenaltyProgram

namespace OAI

/-! # Exact binary penalty evaluation for the selected-root forest

The signed affine and fraction programs compute the root-specific
geometric penalty from its explicit input metadata.
-/

namespace ContingencyTables.RootedPenaltyProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open MatchingFPRAS RootedIntegerEvaluation

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rootCount (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) : ℕ :=
  ∑ a : I⊕J,if RootedPenalty.rootFlag S a then
    (RootedRootPenalty.signedResidual A S x q 0 a).natAbs else 0

lemma rootCount_cast (A : Instance I J) (S : Selection A.T) (x q : I → J → ℤ) :
    (rootCount A S x q:ℝ)=RootedScaledPenalty.rootConstant A S x q := by
  unfold rootCount RootedScaledPenalty.rootConstant
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  · exact Nat.cast_zero

noncomputable def rationalPenalty (A : Instance I J) (S : Selection A.T)
    (C : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) : ℚ :=
  C*((rootCount A S x q:ℚ)+∑ t : TreeCell A.T,max 0 (max
    (-rationalScaledTree A S (CompanionOracleDensity.rationalBinWidth A C) x q v t)
    (rationalScaledTree A S (CompanionOracleDensity.rationalBinWidth A C) x q v t-1)))

theorem rationalPenalty_cast (A : Instance I J) (S : Selection A.T)
    (C : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) :
    (rationalPenalty A S C x q v:ℝ)=RootedScaledPenalty.penalty A S C
      (CompanionOracleDensity.binWidth A C) x q (fun f => (v f:ℝ)) := by
  simp only [rationalPenalty,RootedScaledPenalty.penalty,ForestScaledPenalty.intervalCost,
    Rat.cast_mul,Rat.cast_natCast,Rat.cast_add,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Rat.cast_neg,Rat.cast_sub,Rat.cast_one,rootCount_cast,rationalScaledTree_cast,
    CompanionOracleDensity.rationalBinWidth_cast]

noncomputable def data (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : ForestPenaltyProgram.Input :=
  ((C,rootCount A S x q),List.ofFn (fun i =>
    forestData A S (CompanionOracleDensity.rationalBinWidth A C) (trees i) x q free v))

theorem penaltyCode_data (A : Instance I J) (S : Selection A.T) (C : ℕ) (hC : 0<C)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (ForestPenaltyProgram.penaltyCode (data A S C x q trees free v))=
      rationalPenalty A S C x q (fun f => (v f:ℚ)) := by
  have hB : 0<CompanionOracleDensity.rationalBinWidth A C := by
    unfold CompanionOracleDensity.rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  rw [ForestPenaltyProgram.penaltyCode_value]
  simp only [data,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    evaluate_forest A S _ hB]
  unfold rationalPenalty
  congr 2
  exact Fintype.sum_equiv trees _ _ (fun _ => rfl)

theorem exponentCode_data (A : Instance I J) (S : Selection A.T) (C a : ℕ) (hC : 0<C)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    ForestPenaltyProgram.exponentCode
        ((a,CompanionOracleDensity.rationalHeight A C),data A S C x q trees free v)=
      ⌊(a:ℚ)/CompanionOracleDensity.rationalHeight A C*
        rationalPenalty A S C x q (fun f => (v f:ℚ))⌋₊ := by
  rw [ForestPenaltyProgram.exponentCode_value,penaltyCode_data A S C hC]

end ContingencyTables.RootedPenaltyProgram

end OAI
