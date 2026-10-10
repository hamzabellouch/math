import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingAmplifiedLaw
import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchBudgetBound

namespace OAI

/-! # Public polynomial bounds for the executed positive counting words -/
namespace ContingencyTables.CountingPositiveWordBound
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def measurePolynomial : Polynomial ℕ := 13*CountingPublicWordBound.controlPolynomial+1
def widthPolynomial : Polynomial ℕ :=
  CountingWordsBound.wordPolynomial+CountingMarkerBounds.paddingPolynomial+2*X+1
def singlePolynomial : Polynomial ℕ :=
  CountingPublicWordBound.controlPolynomial*(widthPolynomial.comp measurePolynomial)
def amplifiedPolynomial : Polynomial ℕ := CountingAmplifiedProgram.budgetPolynomial singlePolynomial

private lemma control_parts (S : ℕ) :
    let M := CountingPublicWordBound.controlPolynomial.eval S
    CountingPublicControls.inputPolynomial.eval S ≤ M ∧
    CountingPublicControls.observationPolynomial.eval S ≤ M ∧
    CountingPublicControls.returnPolynomial.eval S ≤ M ∧
    CountingPublicControls.precisionPolynomial.eval S ≤ M ∧
    CountingTerminalBounds.gridPolynomial.eval S ≤ M ∧
    2048*(CountingTerminalBounds.phasePolynomial.eval S+1) ≤ M ∧ S ≤ M := by
  simp only [CountingPublicWordBound.controlPolynomial,eval_add,eval_mul,eval_ofNat,eval_one,eval_X]
  omega

lemma phaseCount_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CountingPositiveProgram.phaseCount (CountingDirectProgram.request r c b epsilon delta) ≤
      CountingPublicWordBound.controlPolynomial.eval (size r c b epsilon delta) := by
  rw [CountingDirectProgram.request,CountingPositiveProgram.phaseCount_data hEK r c b hne epsilon he]
  change ComputedCountingParameters.phases r c b epsilon ≤ _
  have hs := CountingPublicControls.scalar_bound hEK r c b hne epsilon delta he
  exact (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans
    (control_parts (size r c b epsilon delta)).1

lemma measure_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CompanionUniformPhaseWidth.measure
      (CountingPositiveProgram.prepared (CountingDirectProgram.request r c b epsilon delta)) ≤
      measurePolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let S := size r c b epsilon delta
  let M := CountingPublicWordBound.controlPolynomial.eval S
  have hparts := control_parts S
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,s.H,
      CompanionTargetMixing.restartTime A s.H s.L,s.L],
      x ≤ CountingPublicControls.inputPolynomial.eval S :=
    CountingPublicControls.scalar_bound hEK r c b hne epsilon delta he
  have hp : Fintype.card (Labels A) ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or])).trans hparts.1
  have hW : A.W ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hH : s.H ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hT : CompanionTargetMixing.restartTime A s.H s.L ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hL : s.L ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hc := CountingPublicControls.settings_bounds hEK r c b hne epsilon delta he
  have hN : s.N ≤ M := hc.1.trans hparts.2.1
  have hn : s.n ≤ M := hc.2.1.trans hparts.2.2.1
  have hk : s.k ≤ M := hc.2.2.trans hparts.2.2.2.1
  have ht := CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he
  have hK : s.K ≤ M := ht.1.trans hparts.2.2.2.2.1
  have hh : s.h ≤ M :=
    (Nat.mul_le_mul_left 2048 (Nat.add_le_add_right ht.2.2 1)).trans hparts.2.2.2.2.2.1
  have hd : A.d ≤ M := (dimension_le r c b epsilon delta).trans hparts.2.2.2.2.2.2
  have hheight : CompanionOracleDensity.rationalHeight A s.C ≤ M := hH
  have hkdata := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at hkdata
  have hf := CompanionUniformPhaseWidth.fields_data A s
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hkdata (show s.h=CountingPhaseSchedule.initialPrecision s.H from rfl)
  rw [CountingDirectProgram.request,CountingPositiveProgram.prepared_data hEK r c b hne epsilon he]
  unfold CompanionUniformPhaseWidth.measure
  rw [hf]
  simp only [List.sum_cons,List.sum_nil,measurePolynomial,eval_add,eval_mul,eval_ofNat,eval_one]
  dsimp only [M,S] at hp hW hH hT hL hN hn hk hK hh hd hheight
  omega

lemma width_value (req : CountingDirectProgram.Request) :
    CountingPositiveProgram.phaseWidth req=widthPolynomial.eval
      (CompanionUniformPhaseWidth.measure (CountingPositiveProgram.prepared req)) := by
  simp only [CountingPositiveProgram.phaseWidth,CompanionUniformPhaseWidth.width_value,
    widthPolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

theorem single_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta) ≤
      singlePolynomial.eval (size r c b epsilon delta) := by
  have hH := phaseCount_public hEK r c b hne epsilon delta he
  have hM := measure_public hEK r c b hne epsilon delta he
  have hW := polynomial_eval_monotone widthPolynomial hM
  dsimp only at hW
  rw [←width_value] at hW
  simpa only [CountingPositiveProgram.bitCount,singlePolynomial,eval_mul,eval_comp] using
    Nat.mul_le_mul hH hW

theorem amplified_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount
      (CountingDirectProgram.request r c b epsilon delta) ≤
      amplifiedPolynomial.eval (size r c b epsilon delta) :=
  CountingAmplifiedProgram.budget_bound CountingPositiveProgram.bitCount singlePolynomial
    r c b epsilon delta hd (single_public hEK r c b hne epsilon delta he)

theorem branch_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta) :
    CountingBranchProgram.publicBudget
      (CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount)
      (Algorithms.encodeCountingInput r c b epsilon delta) ≤
      (CountingBranchProgram.budgetPolynomial amplifiedPolynomial).eval
        (size r c b epsilon delta) := by
  exact CountingBranchProgram.publicBudget_bound hEK
    (CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount) amplifiedPolynomial
    (fun _ _ r c b hne epsilon delta he hd => amplified_public hEK r c b hne epsilon delta he hd)
    m n r c b epsilon delta he hd

end
end ContingencyTables.CountingPositiveWordBound

end OAI
