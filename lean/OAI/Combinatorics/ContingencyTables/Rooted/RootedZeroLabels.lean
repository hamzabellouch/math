import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWeightOracle

namespace OAI

/-! # Counting when the retained small cells have no positive capacities

The paired transversal space then has one state. The terminal total is
one actual free-assignment weight, so the bounded-word
weight estimator applies directly; no Markov restart is needed.
-/

namespace ContingencyTables.RootedZeroLabels

open CommonBasesFPRAS CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CompanionWeightOracle CompanionTerminalMass CompanionTerminalApplication
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma small_capacity_zero (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (s : SmallCell A) : A.b s.val.1 s.val.2=0 := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  by_contra hn
  exact isEmptyElim (⟨s,⟨0,Nat.pos_of_ne_zero hn⟩⟩ : Labels A)

lemma profile_zero (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (S : Set (Labels A×Bool)) : profile A S=fun _ => 0 := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  funext u
  simp only [profile,LabelledFactorial.groupCount,Finset.univ_eq_empty,
    Finset.filter_empty,Finset.card_empty]

lemma factorialRatio_one (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (S : Set (Labels A×Bool)) : factorialRatio A S=1 := by
  simp only [factorialRatio,factorialNumerator,factorialDenominator,profile_zero A hzero]
  have hz (s : SmallCell A) : A.b s.val.1 s.val.2=0 := small_capacity_zero A hzero s
  simp only [hz,Nat.factorial_zero,Finset.prod_const_one,Nat.cast_one,div_self (one_ne_zero : (1:ℚ) ≠ 0)]

lemma total_eq_h (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (hzero : Fintype.card (Labels A)=0) (C : ℕ) (hC : 0 < C) (j : ℕ) :
    RootedWarmStart.total A R j=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (fun _ => 0) := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  have hp : (pairs : List (Pair A))=[] := by
    simp only [pairs,Finset.univ_eq_empty,Finset.toList_empty,List.map_nil]
  rw [RootedWarmStart.total,hp,slotTotal_nil,RootedWeightOracle.weight_source A R C hC,
    profile_zero A hzero,factorialRatio_one A hzero]
  simp only [Rat.cast_one,mul_one]

/-- The direct all-large branch has arbitrary confidence using the
same actual finite-word evaluator, with no positive-label premise. -/
theorem success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (hzero : Fintype.card (Labels A)=0) (E : Endpoints A)
    (C K L : ℕ) (hC : 0 < C) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (hW' : 20*A.d ≤ A.W)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hH : finalPhase A L (epsilon:ℝ) ≤ rationalHeight A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits :
      Fin (medianEstimatorBits A C K (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta) → Bool =>
        let value := RootedOracleDensity.medianEstimate A R C (fun _ => 0) K hK hW
          (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta v bits
        if (1-(epsilon:ℝ))*tableCount A ≤ (value:ℝ) ∧
          (value:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have heR1 : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  have hterminal := RootedTerminalApplication.terminal_normalizer A R E L epsilon
    heR heR1 hW' hL
  have ht := total_eq_h A R hzero C hC (finalPhase A L (epsilon:ℝ))
  rw [ht] at hterminal
  have hm := RootedOracleDensity.medianEstimate_success A R C hC (fun _ => 0)
    (by intro u; exact Nat.zero_le _) K hK hW hB
    (finalPhase A L (epsilon:ℝ)) hH (epsilon/2) delta
    (by positivity) (by linarith) hd hPL hCheeger v
  apply hm.trans
  apply uniformAverage_mono
  intro bits
  let value := RootedOracleDensity.medianEstimate A R C (fun _ => 0) K hK hW
    (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta v bits
  by_cases hgood :
      (1-((epsilon/2:ℚ):ℝ))*RootedCountIdentification.h A R
        ((finalPhase A L (epsilon:ℝ):ℝ)*C/height A C) (fun _ => 0) ≤ (value:ℝ) ∧
      (value:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*RootedCountIdentification.h A R
        ((finalPhase A L (epsilon:ℝ):ℝ)*C/height A C) (fun _ => 0)
  · have hlo := mul_le_mul_of_nonneg_left hterminal.1
      (show 0 ≤ 1-(epsilon:ℝ)/2 by linarith)
    have hhi := mul_le_mul_of_nonneg_left hterminal.2
      (show 0 ≤ 1+(epsilon:ℝ)/2 by linarith)
    have hZ := tableCount_ge_one A
    have hout : (1-(epsilon:ℝ))*tableCount A ≤ (value:ℝ) ∧
        (value:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A := by
      simp only [Rat.cast_div,Rat.cast_ofNat] at hgood
      constructor
      · nlinarith
      · nlinarith [mul_nonneg heR.le (show 0 ≤ tableCount A by linarith)]
    dsimp only [value] at hgood hout
    simp only [hgood,hout,le_refl]
  · dsimp only [value] at hgood
    simp only [hgood,ite_false]
    split_ifs <;> norm_num

end
end ContingencyTables.RootedZeroLabels

end OAI
