import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleWalkProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogWalk
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

def proposalWidth (z : Frame) : ℕ := Nat.clog 2 (8*z.2.1.1.1)
def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : Frame => z.2.1.1.1) :=
    composition (composition (composition second first) first) first
  let M : Realizer (fun z : Frame => 8*z.2.1.1.1) :=
    composition (f := fun z : Frame => (8,z.2.1.1.1))
      (g := fun x : ℕ×ℕ => x.1*x.2) (pair (constant 8) D) multiply
  exact composition (f := fun z : Frame => 8*z.2.1.1.1)
    (g := Nat.clog 2) M ceilLogTwoRealizer
lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (composition (composition (second (A := ℕ) (B := RootedPenaltyEvaluateProgram.Parameters×
        RootedDemandProgram.Input)) first) first) first) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_first
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

def stepWidth (z : Frame) : ℕ := proposalWidth z+RootedPenaltyEvaluateProgram.height z.2.1
def stepWidthRealizer : Realizer stepWidth :=
  composition (f := fun z : Frame => (proposalWidth z,RootedPenaltyEvaluateProgram.height z.2.1))
    (g := fun x : ℕ×ℕ => x.1+x.2)
    (pair proposalWidthRealizer
      (composition (f := fun z : Frame => z.2.1) (g := RootedPenaltyEvaluateProgram.height)
        (composition second first) RootedPenaltyEvaluateProgram.heightRealizer)) add
lemma polynomial_stepWidth : PolynomialTime stepWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_proposalWidth
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_height)) polynomial_add

def flatWalk (z : State×List Bool) : State :=
  walkWords (z.1,wordChunks (stepWidth z.1.1,z.2))
def flatWalkRealizer : Realizer flatWalk :=
  composition (f := fun z : State×List Bool => (z.1,wordChunks (stepWidth z.1.1,z.2)))
    (g := walkWords)
    (pair first (composition (f := fun z : State×List Bool => (stepWidth z.1.1,z.2))
      (g := wordChunks)
      (pair (composition (f := fun z : State×List Bool => z.1.1) (g := stepWidth)
        (composition first first) stepWidthRealizer) second) wordChunksRealizer)) walkWordsRealizer
theorem polynomial_flatWalk : PolynomialTime flatWalkRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_stepWidth) polynomial_second) polynomial_wordChunks)) polynomial_walkWords

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

noncomputable section
variable {m n : ℕ}

lemma stepWidth_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    stepWidth (data A C a K z v).1=CompanionOracleDensity.oracleStepBits A C := by
  change Nat.clog 2 (8*A.d)+RootedPenaltyEvaluateProgram.height ((A.d,A.W),(C,a))=_
  rw [RootedPenaltyEvaluateProgram.height_data]
  rfl

lemma stepWidth_pos (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0 < C) :
    0 < CompanionOracleDensity.oracleStepBits A C := by
  have hd : 0 < A.d := lt_of_lt_of_le Nat.zero_lt_one A.hd
  have hh : 0 < CompanionOracleDensity.rationalHeight A C := by
    unfold CompanionOracleDensity.rationalHeight
    positivity
  exact hh.trans_le (Nat.le_add_left _ _)

/-- Every flat input bit is split into the prescribed independent step
words, and the polynomial program computes their literal finite walk. -/
theorem flatWalk_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N : ℕ) (bits : Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool) :
    flatWalk (data A C a K z v,List.ofFn bits)=
      data A C a K z (wordWalk (RootedCatalogGrid.bitStep A C a z) v N
        (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C) bits)) := by
  unfold flatWalk
  rw [stepWidth_data,wordChunks_ofFn (stepWidth_pos A C hC) bits]
  exact walkWords_ofFn A C a K hC z v N _

def flatGridWalk (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool) :
    Grid (I := Fin (RootedCatalogGrid.freeCount A)) K :=
  wordWalk (RootedCatalogGrid.bitStep A C a z) v N
    (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C) bits)

lemma flatGridWalk_law (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    mapLaw (uniformLaw (α := Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool))
      (flatGridWalk A C a z v N)=wordWalkLaw (RootedCatalogGrid.bitStep A C a z) v N := by
  unfold flatGridWalk
  rw [←FairBits.map_equiv (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C)),
    FairBits.uniform_equiv]
  rfl

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
