import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingWords
import OAI.Combinatorics.ContingencyTables.Rooted.RootedZeroLabels

namespace OAI

/-! # The computed zero-label counting branch

When all retained capacities vanish, the actual direct weight estimator
replaces the phase walk. Its target is still the original bounded-table
count, transported through the executed endpoint translation.
-/

namespace ContingencyTables.ComputedCountingZero

open CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open CompanionOracleDensity CompanionTerminalApplication
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def zeroBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) : ℕ :=
  medianEstimatorBits (data hEK r c b hne epsilon he) (coefficient r c b epsilon)
    (binCount r c b epsilon)
    (finalPhase (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ))
    ((epsilon/2)/2) delta

def zeroEstimate (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) (bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedOracleDensity.medianEstimate (data hEK r c b hne epsilon he)
    (ComputedCountingWords.root hEK r c b hne epsilon he) (coefficient r c b epsilon)
    (fun _=>0) (binCount r c b epsilon) (binCount_pos r c b epsilon he)
    (cutoff_eq hEK r c b hne epsilon he).ge
    (finalPhase (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ))
    ((epsilon/2)/2) delta (start hEK r c b hne epsilon he) bits

theorem zero_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hzero : Fintype.card (Labels (data hEK r c b hne epsilon he))=0) :
    1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
      if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := by
  let A:=data hEK r c b hne epsilon he
  let K:=binCount r c b epsilon
  have hK: 1≤K:=binCount_pos r c b epsilon he
  have hW: 100*A.d*K≤A.W:=(cutoff_eq hEK r c b hne epsilon he).ge
  have hW': 20*A.d≤A.W := by
    have hh:=Nat.mul_le_mul_left (100*A.d) hK
    simp only [Nat.mul_one] at hh
    exact (show 20*A.d≤100*A.d by omega).trans (hh.trans hW)
  have hL: (∏ a : Fin m×Fin n,(A.b a.1 a.2+1))≤2^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.capacity_product_bound A
  have hH: finalPhase A (capacityBits r c b) ((epsilon/2:ℚ):ℝ)≤
      rationalHeight A (coefficient r c b epsilon) :=
    (phases_final hEK r c b hne epsilon he).symm.trans_le
      (phases_height hEK r c b hne epsilon he).le
  have hcount: CompanionTerminalMass.tableCount A=(Fintype.card (BoundedTable r c b):ℝ) :=
    ComputedCompanionInstance.original_count hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)
  have hs:=RootedZeroLabels.success A (ComputedCountingWords.root hEK r c b hne epsilon he)
    hzero (ComputedCompanionInstance.endpoints hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)) (coefficient r c b epsilon) K (capacityBits r c b)
    (coefficient_pos r c b epsilon he) hK hW (binCount_cast hEK r c b hne epsilon he) hW'
    (epsilon/2) delta (by positivity) (by linarith) hd hL hH
    (hPL _) (hCheeger _ _) (start hEK r c b hne epsilon he)
  rw [hcount] at hs
  dsimp only [A,K] at hs
  have hs': 1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
      if (1-((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := hs
  apply hs'.trans
  apply uniformAverage_mono
  intro bits
  have hZ: (0:ℝ)≤Fintype.card (BoundedTable r c b):=Nat.cast_nonneg _
  have heR: (0:ℝ)<epsilon:=by exact_mod_cast he
  by_cases hh:
      (1-((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
  · have hout:
        (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
            (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
            (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) := by
      simp only [Rat.cast_div,Rat.cast_ofNat] at hh
      constructor <;> nlinarith [mul_nonneg heR.le hZ]
    simp only [hh,hout,le_refl]
  · simp only [hh,ite_false]
    split_ifs <;> norm_num

end
end ContingencyTables.ComputedCountingZero

end OAI
