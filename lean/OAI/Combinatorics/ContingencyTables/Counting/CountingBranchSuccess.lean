import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSuccess
import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchMachine

namespace OAI

/-! # Accuracy of the public dispatcher from its positive counting branch -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

abbrev Accurate (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (q : ℚ) : Prop :=
  (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤ (q:ℝ) ∧
    (q:ℝ) ≤ (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)

theorem success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (positive : Input→TreeFraction.Fraction) (width : Request→ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hpositive : ∀ hne : ∃ X,TableTightening.Feasible r c b X,
      0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) →
      1-(delta:ℝ) ≤ uniformAverage
        (fun bits : Fin (width (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          if Accurate r c b epsilon (TreeFraction.val (positive
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0)) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (budget width (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        if Accurate r c b epsilon (TreeFraction.val (output positive
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0) := by
  let req := CountingDirectProgram.request r c b epsilon delta
  change 1-(delta:ℝ) ≤ uniformAverage
    (fun bits : Fin (budget width req)→Bool =>
      if Accurate r c b epsilon (TreeFraction.val (output positive (req,List.ofFn bits)))
        then (1:ℝ) else 0)
  by_cases hf : feasible req=true
  · have hne := (feasible_data hEK r c b epsilon delta).mp hf
    by_cases hz : direct req=true
    · rw [budget_direct width req hf hz]
      simp_rw [output_direct positive req hf hz]
      exact CountingDirectProgram.success hEK hPL hCheeger r c b hne epsilon delta he he1 hd
        ((direct_data hEK r c b hne epsilon delta he).mp hz)
    · have hz' := Bool.eq_false_iff.mpr hz
      rw [budget_positive width req hf hz']
      simp_rw [output_positive positive req hf hz']
      exact hpositive hne (Nat.pos_of_ne_zero (fun h => hz
        ((direct_data hEK r c b hne epsilon delta he).mpr h)))
  · have hf' := Bool.eq_false_iff.mpr hf
    have hzero := (count_zero_iff_rejected hEK r c b epsilon delta).mpr hf'
    have hz : Fintype.card (BoundedTable r c b)=0 := hzero
    simp_rw [output_rejected positive req hf',Accurate,hz,Nat.cast_zero,mul_zero]
    norm_num [TreeFraction.val,uniformAverage_const]
    exact_mod_cast hd.le

end
end ContingencyTables.CountingBranchProgram

end OAI
