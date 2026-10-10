import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleFlatProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRatioSamples

namespace OAI

/-! # Polynomial execution of an adjacent-parameter ratio sample

The exact ratio is either one or one half. The program compares the two
computed integer exponents and never materializes an exponential weight.
-/

namespace ContingencyTables.RootedRatioSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev Input := RootedPenaltyEvaluateProgram.Input

def bump (z : Input) : Input := ((z.1.1,(z.1.2.1,z.1.2.2+1)),z.2)
def bumpRealizer : Realizer bump :=
  pair (pair (composition first first)
    (pair (composition (composition first second) first)
      (composition (composition (composition first second) second) successor))) second
lemma polynomial_bump : PolynomialTime bumpRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second)
          polynomial_successor))) polynomial_second

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate

def equalExponents (z : Input) : Bool :=
  decide (RootedPenaltyEvaluateProgram.evaluate (bump z)=RootedPenaltyEvaluateProgram.evaluate z)
def equalExponentsRealizer : Realizer equalExponents :=
  composition (f := fun z : Input => (RootedPenaltyEvaluateProgram.evaluate (bump z),
    RootedPenaltyEvaluateProgram.evaluate z)) (g := fun x : ℕ×ℕ => decide (x.1=x.2))
    (pair (composition (f := bump) (g := RootedPenaltyEvaluateProgram.evaluate)
      bumpRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)
      RootedPenaltyEvaluateProgram.evaluateRealizer) natEqual
lemma polynomial_equalExponents : PolynomialTime equalExponentsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_bump RootedPenaltyEvaluateProgram.polynomial_evaluate)
    RootedPenaltyEvaluateProgram.polynomial_evaluate) polynomial_natEqual

def ratio (z : Input) : TreeFraction.Fraction := if equalExponents z then (1,1) else (1,2)
def ratioRealizer : Realizer ratio :=
  choose equalExponentsRealizer (constant (1,1)) (constant (1,2))
lemma polynomial_ratio : PolynomialTime ratioRealizer :=
  polynomial_choose polynomial_equalExponents (polynomial_constant _) (polynomial_constant _)

abbrev SampleInput := RootedOracleWalkProgram.State×List Bool

def currentInput (z : SampleInput) : Input :=
  (RootedOracleWalkProgram.toData (RootedOracleWalkProgram.flatWalk z)).2
def currentInputRealizer : Realizer currentInput :=
  composition (f := RootedOracleWalkProgram.flatWalk)
    (g := fun z : RootedOracleWalkProgram.State => (RootedOracleWalkProgram.toData z).2)
    RootedOracleWalkProgram.flatWalkRealizer
    (composition RootedOracleWalkProgram.toDataRealizer second)
lemma polynomial_currentInput : PolynomialTime currentInputRealizer :=
  polynomial_composition RootedOracleWalkProgram.polynomial_flatWalk
    (polynomial_composition RootedOracleWalkProgram.polynomial_toData polynomial_second)

def output (z : SampleInput) : TreeFraction.Fraction := ratio (currentInput z)
def outputRealizer : Realizer output :=
  composition (f := currentInput) (g := ratio) currentInputRealizer ratioRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_currentInput polynomial_ratio

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedCompletion
open scoped BigOperators

noncomputable section
variable {m n : ℕ}

private lemma exponent_step (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v ∨
    RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v+1 := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hd := RootedOracleDensity.D_bounds A (rowColumn A.T) C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hi : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hi := (v i).property.2; omega)
      exact hi.trans hKB)
  let x := (a:ℝ)/height A C*RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)
  let q := RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)/height A C
  have hheight := height_positive A C hCR
  have hq0 : 0 ≤ q := div_nonneg hd.1 hheight.le
  have hq1 : q ≤ 1 := (div_le_one hheight).mpr hd.2
  have he : (((a+1:ℕ):ℝ)/height A C)*RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)=x+q := by
    dsimp only [x,q]
    push_cast
    ring
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  have hs : ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by omega
  have h0 := RootedOracleDensity.gridExponent_eq_floor A (rowColumn A.T) C a z v
  have h1 := RootedOracleDensity.gridExponent_eq_floor A (rowColumn A.T) C (a+1) z v
  rw [he] at h1
  rcases hs with hs|hs
  · left
    exact_mod_cast h1.trans (hs.trans h0.symm)
  · right
    have hh : (RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v:ℤ)=
        (RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v:ℤ)+1 := by
      rw [h1,hs,h0]
    exact_mod_cast hh

lemma ratio_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    TreeFraction.val (ratio (RootedOracleStepProgram.data A C a K z v).2)=
      RootedOracleDensity.rationalRatioObservable A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) := by
  have hb : bump (RootedOracleStepProgram.data A C a K z v).2=
      (RootedOracleStepProgram.data A C (a+1) K z v).2 := rfl
  unfold ratio equalExponents
  rw [hb,RootedOracleStepProgram.evaluate_data A C (a+1) K hC,
    RootedOracleStepProgram.evaluate_data A C a K hC]
  rcases exponent_step A C a hC z hz hKB (RootedCatalogGrid.gridEquiv A K v) with he|he
  · simp only [RootedCatalogGrid.exponent,he,decide_true,ite_true,TreeFraction.val,
      Nat.cast_one,div_self (by norm_num : (1:ℚ)≠0),
      RootedOracleDensity.rationalRatioObservable,RootedOracleDensity.rationalGridWeight]
    exact (div_self (by positivity)).symm
  · have hn : RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z
        (RootedCatalogGrid.gridEquiv A K v)≠RootedOracleDensity.gridExponent A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) := by omega
    simp only [RootedCatalogGrid.exponent,hn,decide_false,Bool.false_eq_true,ite_false]
    simp only [TreeFraction.val,Nat.cast_one,Nat.cast_ofNat,RootedOracleDensity.rationalRatioObservable,
      RootedOracleDensity.rationalGridWeight,he,pow_succ]
    field_simp

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) :
    TreeFraction.val (output (RootedOracleWalkProgram.data A C a K z v,List.ofFn bits))=
      RootedOracleDensity.rationalRatioObservable A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K (RootedOracleWalkProgram.flatGridWalk A C a z v N bits)) := by
  unfold output currentInput
  rw [RootedOracleWalkProgram.flatWalk_data A C a K hC z v N bits]
  exact ratio_data A C a K hC z hz hKB _

end
end ContingencyTables.RootedRatioSampleProgram

end OAI
