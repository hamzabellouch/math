import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingParameters

namespace OAI

/-! # The actual counting experiment on original bounded-table inputs

This is the positive-label branch of the computed-input experiment.
Its output is the stored adaptive rational estimate, after independent
median amplification. Only the cited analytic/flow inputs are external.
-/

namespace ContingencyTables.ComputedCountingWords

open CompanionFactorialApplication CommonBasesFPRAS GridBoundary
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def root (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    RootedCompletion.Selection (data hEK r c b hne epsilon he).T :=
  RootedCompletion.rowColumn _

def bitCount (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) : ℕ :=
  RootedCountingAmplification.bitCount (data hEK r c b hne epsilon he)
    (settings hEK r c b hne epsilon he) delta

def estimate (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) (bits : Fin (bitCount hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedCountingAmplification.estimate (data hEK r c b hne epsilon he)
    (root hEK r c b hne epsilon he) (settings hEK r c b hne epsilon he) delta bits

/-- The computed preprocessing and schedule satisfy every input of the
proved adaptive-history theorem. There is no supplied forest, baseline,
endpoint table, or oracle-error assumption in this statement. -/
theorem positive_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hp : 0<Fintype.card (Labels (data hEK r c b hne epsilon he))) :
    1-(delta:ℝ)≤uniformAverage (fun bits : Fin (bitCount hEK r c b hne epsilon he delta)→Bool =>
      if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (estimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (estimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := by
  let A:=data hEK r c b hne epsilon he
  let K:=binCount r c b epsilon
  have hK : 1≤K:=binCount_pos r c b epsilon he
  have hW : 100*A.d*K≤A.W:=(cutoff_eq hEK r c b hne epsilon he).ge
  have hW' : 20*A.d≤A.W := by
    have hh:=Nat.mul_le_mul_left (100*A.d) hK
    simp only [Nat.mul_one] at hh
    exact (show 20*A.d≤100*A.d by omega).trans (hh.trans hW)
  have hL : (∏ a : Fin m×Fin n,(A.b a.1 a.2+1))≤2^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.capacity_product_bound A
  have hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1))≤
      (2:ℝ)^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.small_product_bound A
  have hcount : CompanionTerminalMass.tableCount A=(Fintype.card (BoundedTable r c b):ℝ) :=
    ComputedCompanionInstance.original_count hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)
  have hs:=RootedCountingAmplification.success A (root hEK r c b hne epsilon he)
    (coefficient r c b epsilon) K (phases r c b epsilon) (capacityBits r c b)
    hK hW epsilon delta he he1 hd (start hEK r c b hne epsilon he)
    (ComputedCompanionInstance.endpoints hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)) hW' hL
    (phases_final hEK r c b hne epsilon he) (coefficient_pos r c b epsilon he)
    (binCount_cast hEK r c b hne epsilon he) (phases_height hEK r c b hne epsilon he).le
    hbox (hPL _) (hCheeger _ _) hp
  rw [hcount] at hs
  exact hs

end
end ContingencyTables.ComputedCountingWords

end OAI
