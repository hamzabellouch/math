import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleStepProgram

namespace OAI

/-! # A single fixed word drives an executed oracle transition -/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev WordInput := Data×List Bool

def proposalWidth (z : WordInput) : ℕ := Nat.clog 2 (8*z.1.2.1.1.1)
def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : WordInput => z.1.2.1.1.1) :=
    composition (composition (composition (composition first second) first) first) first
  let M : Realizer (fun z : WordInput => 8*z.1.2.1.1.1) :=
    composition (f := fun z : WordInput => (8,z.1.2.1.1.1))
      (g := fun x : ℕ×ℕ => x.1*x.2) (pair (constant 8) D) multiply
  exact composition (f := fun z : WordInput => 8*z.1.2.1.1.1)
    (g := Nat.clog 2) M ceilLogTwoRealizer
lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (composition (composition (composition (first (A := Data) (B := List Bool)) second)
        first) first) first) :=
    polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_first) polynomial_first
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

def wordStep (z : WordInput) : List ℕ :=
  step (z.1,(z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))
def wordStepRealizer : Realizer wordStep :=
  composition (f := fun z : WordInput =>
    (z.1,(z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))) (g := step)
    (pair first (pair
      (composition (pair second proposalWidthRealizer) takeFast)
      (composition (pair second proposalWidthRealizer) dropFast))) stepRealizer
theorem polynomial_wordStep : PolynomialTime wordStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth)
      polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth)
      polynomial_dropFast))) polynomial_step

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

noncomputable section
variable {m n : ℕ}

/-- Exact code agreement for the prescribed finite word, including
unused direction codes and unsuccessful acceptance tests. -/
theorem wordStep_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (bits : Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    wordStep (data A C a K z v,List.ofFn bits)=
      gridNatCode (RootedCatalogGrid.bitStep A C a z v bits) := by
  have ht := ofFn_split_take (p := Nat.clog 2 (8*A.d))
    (k := CompanionOracleDensity.rationalHeight A C) bits
  have hd := ofFn_split_drop (p := Nat.clog 2 (8*A.d))
    (k := CompanionOracleDensity.rationalHeight A C) bits
  have hp : ((List.ofFn bits).take (Nat.clog 2 (8*A.d)),
      (List.ofFn bits).drop (Nat.clog 2 (8*A.d)))=
      (List.ofFn (splitWordEquiv (Nat.clog 2 (8*A.d))
        (CompanionOracleDensity.rationalHeight A C) bits).1,
       List.ofFn (splitWordEquiv (Nat.clog 2 (8*A.d))
        (CompanionOracleDensity.rationalHeight A C) bits).2) := Prod.ext ht hd
  have hsplit := congrArg (fun coins => step (data A C a K z v,coins)) hp
  change step (data A C a K z v,((List.ofFn bits).take (Nat.clog 2 (8*A.d)),
    (List.ofFn bits).drop (Nat.clog 2 (8*A.d))))=_
  refine hsplit.trans ((step_pair A C a K hC z v
    (splitWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1
    (splitWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).2).trans ?_)
  change gridNatCode (match axisCodeStep v
      (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1 with
    | Option.none => v
    | Option.some w => if acceptDyadic
        (RootedCatalogGrid.exponent A C a z w-RootedCatalogGrid.exponent A C a z v)
        (CompanionOracleDensity.rationalHeight A C)
        (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).2
      then w else v)=_
  unfold RootedCatalogGrid.bitStep
  dsimp only
  cases axisCodeStep v
    (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1 with
  | none => rfl
  | some w => rfl

end
end ContingencyTables.RootedOracleStepProgram

end OAI
