import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleKernel
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisBits
import OAI.Combinatorics.ContingencyTables.Transport.DyadicAcceptance
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMetropolis
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

namespace OAI

/-! # A fixed finite Boolean experiment for each actual evaluator transition -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_acceptance_finite_coin (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v w : Grid (I := Fin (dimension A)) K) :
    ((Finset.univ.filter (acceptDyadic
      (gridExponent A C a z w-gridExponent A C a z v) (rationalHeight A C))).card:ℝ)/
        (2:ℝ)^rationalHeight A C=
      min 1 (gridWeight A C a z w/gridWeight A C a z v) := by
  rw [acceptDyadic_probability]
  · rw [gridWeight_eq_dyadic,gridWeight_eq_dyadic,dyadic_ratio_min]
  · exact (Nat.sub_le _ _).trans ((gridExponent_upper A C a hC z hz hKB w).trans haH)

def finiteOracleStepLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A C a z w-gridExponent A C a z v) (rationalHeight A C))

/-- Every valid direction has one code; unused directions, boundary
proposals and failed dyadic tests stay at the starting vertex. -/
theorem finiteOracleStepLaw_eq (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    finiteOracleStepLaw A C a z v=oracleTransitionLaw A C a z hK v := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hwv
  apply Rat.cast_injective (α := ℝ)
  change ((finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A C a z w-gridExponent A C a z v)
      (rationalHeight A C))).mass w:ℝ)=(oracleTransition A C a z v w:ℝ)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hwv.symm,
    axisCodeStep_count (dense_proposal_code_bound A.d (dimension A) (ForestScaledPenalty.free_card_le A))]
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  push_cast
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2^rationalHeight A C)))
    (acceptDyadic (gridExponent A C a z w-gridExponent A C a z v) (rationalHeight A C))
    (fun bits => Classical.propDecidable _)]
  rw [oracle_acceptance_finite_coin A C a hC haH z hz hKB v w]
  unfold oracleTransition
  rw [ite_eq_right hwv.symm,add_zero,oracleMove_cast]
  unfold MetropolisChain.move binProposal
  by_cases hvw : Neighbor v w <;> simp [hvw]

def oracleStepBits (A : Instance I J) (C : ℕ) : ℕ :=
  Nat.clog 2 (8*A.d)+rationalHeight A C

def oracleBitStep (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (oracleStepBits A C) → Bool) : Grid (I := Fin (dimension A)) K :=
  let draw := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C) bits
  match axisCodeStep v draw.1 with
  | none => v
  | some w => if draw.2.val < 2^(rationalHeight A C-(gridExponent A C a z w-gridExponent A C a z v))
      then w else v

def oracleBitStepLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (oracleBitStep A C a z v)

lemma oracleBitStepLaw_eq_finite (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A C a z v=finiteOracleStepLaw A C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A C a z w-gridExponent A C a z v) (rationalHeight A C))
  have hf : oracleBitStep A C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [oracleBitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold oracleBitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

theorem oracleBitStepLaw_eq (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A C a z v=oracleTransitionLaw A C a z hK v := by
  rw [oracleBitStepLaw_eq_finite]
  exact finiteOracleStepLaw_eq A C a hC haH z hz hK hKB v

def oracleBitWalkLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  wordWalkLaw (oracleBitStep A C a z) v n

/-- A fixed rectangular Boolean array realizes the complete independent
finite walk whose mixing estimate was proved for the real chain. -/
theorem oracleBitWalkLaw_eq (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    oracleBitWalkLaw A C a z v n=oracleWalkLaw A C a z hK v n := by
  unfold oracleBitWalkLaw oracleWalkLaw
  rw [wordWalkLaw_eq]
  have he : (fun w : Grid (I := Fin (dimension A)) K =>
      mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (oracleBitStep A C a z w))=
      oracleTransitionLaw A C a z hK := by
    funext w
    exact oracleBitStepLaw_eq A C a hC haH z hz hK hKB w
  rw [he]

theorem oracleBitWalkLaw_variation (A : Instance I J) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (oracleBitWalkLaw A C a z v (oracleTime A C K Q theta))
      (oracleStationaryLaw A C a z hK):ℝ) ≤ theta/(8*Q) := by
  rw [oracleBitWalkLaw_eq A C a hC haH z hz hK hKB]
  apply oracleWalkLaw_variation A C a theta hC _ htheta z hz K Q hK hQ hKB hPL hCheeger v
  rw [←rationalHeight_cast]
  exact_mod_cast haH

end

end ContingencyTables.CompanionOracleDensity

end OAI
