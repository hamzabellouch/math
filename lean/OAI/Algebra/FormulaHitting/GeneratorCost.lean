import OAI.Algebra.FormulaHitting.Program
import OAI.Algebra.FormulaHitting.ProgramCost

namespace OAI

namespace NCHitting

open BitModel

def generatorExpressionBudget (M : ℕ) : ℕ :=
  expressionBudget M (intermediateWidthBound M) (registerReadBound M)

def entryCostBound (M : ℕ) : ℕ :=
  20 * generatorExpressionBudget M + intermediateWidthBound M + 20

def entryOutputBound (M : ℕ) : ℕ := intermediateWidthBound M + 3

private theorem bounded_dimensionExpr {environment : List ℕ} {M nr sr n s : ℕ}
    (hM : 2 ≤ M) (hlen : environment.length ≤ 5)
    (henv : ∀ a ∈ environment, a ≤ M) (hnr : nr ≤ 4) (hsr : sr ≤ 4)
    (hnread : environment[nr]?.getD 0 = n) (hsread : environment[sr]?.getD 0 = s)
    (hn : n ≤ M) (hs : s ≤ M) :
    (dimensionExpr nr sr).Bounded environment M
      (intermediateWidthBound M) (registerReadBound M) := by
  have htwo := Expr.bounded_literal (environment := environment) hM
  have hnvar := Expr.bounded_read hlen hnr henv
  have hsvar := Expr.bounded_read hlen hsr henv
  have hsn : s.size ≤ M := (size_le_self s).trans hs
  have hwn : width n ≤ M + 1 := width_le_of_le hn
  have hws2 : width (s ^ 2) ≤ 2 + 2 * M := by
    have h := width_pow_le s 2
    omega
  have hw2n : width (2 * n) ≤ M + 4 := by
    have h := width_mul_le 2 n
    have ht : width 2 = 3 := rfl
    omega
  have hp : (Expr.power (.read sr) (.literal 2)).Bounded environment M
      (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, hsvar, htwo, ?_, ?_⟩
    · simp only [Expr.run, powerRun_value, hsread]
      unfold intermediateWidthBound
      omega
    · simpa only [Expr.run, hsread] using hs
    · exact hM
  have hleft : (Expr.mul (.literal 2) (.read nr)).Bounded environment M
      (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, htwo, hnvar⟩
    simp only [Expr.run, hnread]
    unfold intermediateWidthBound
    omega
  refine ⟨?_, hleft, hp⟩
  have hw := width_mul_le (2 * n) (s ^ 2)
  simp only [Expr.run, powerRun_value, hnread, hsread]
  unfold intermediateWidthBound
  omega

theorem dimensionExpr_cost_le {environment : List ℕ} {M nr sr n s : ℕ}
    (hM : 2 ≤ M) (hlen : environment.length ≤ 5)
    (henv : ∀ a ∈ environment, a ≤ M) (hnr : nr ≤ 4) (hsr : sr ≤ 4)
    (hnread : environment[nr]?.getD 0 = n) (hsread : environment[sr]?.getD 0 = s)
    (hn : n ≤ M) (hs : s ≤ M) :
    ((dimensionExpr nr sr).run environment).cost ≤ 7 * generatorExpressionBudget M := by
  have h := Expr.cost_le_nodes_budget environment M (intermediateWidthBound M)
    (registerReadBound M) (dimensionExpr nr sr)
    (bounded_dimensionExpr hM hlen henv hnr hsr hnread hsread hn hs)
  simpa [dimensionExpr, Expr.nodes, generatorExpressionBudget] using h

private theorem bounded_entryExpressions {M q r i n s : ℕ}
    (hM : 2 ≤ M) (hq : q ≤ M) (hr : r ≤ M) (hi : i + 1 ≤ M)
    (hn : n ≤ M) (hs : s ≤ M) :
    let environment := [q, r, i, n, s]
    let bounded := fun e : Expr => e.Bounded environment M
      (intermediateWidthBound M) (registerReadBound M)
    bounded (.less (.read 0) (.read 1)) ∧
    bounded (.odd (.sub (.sub (.read 1) (.read 0)) (.literal 1))) ∧
    bounded (.mul (.read 1) (.power (.add (.read 2) (.literal 1))
      (.sub (.read 1) (.read 0)))) := by
  dsimp only
  have henv : ∀ a ∈ [q, r, i, n, s], a ≤ M := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  have hqv := Expr.bounded_read (environment := [q, r, i, n, s])
    (index := 0) (by simp) (by omega) henv
  have hrv := Expr.bounded_read (environment := [q, r, i, n, s])
    (index := 1) (by simp) (by omega) henv
  have hiv := Expr.bounded_read (environment := [q, r, i, n, s])
    (index := 2) (by simp) (by omega) henv
  have hone := Expr.bounded_literal (environment := [q, r, i, n, s])
    (a := 1) (by omega : 1 ≤ M)
  have hsub : (Expr.sub (.read 1) (.read 0)).Bounded [q, r, i, n, s] M
      (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, hrv, hqv⟩
    simpa [Expr.run] using small_width (by omega : r - q ≤ M)
  have hsubone : (Expr.sub (.sub (.read 1) (.read 0)) (.literal 1)).Bounded
      [q, r, i, n, s] M (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, hsub, hone⟩
    simpa [Expr.run] using small_width (by omega : r - q - 1 ≤ M)
  have hadd : (Expr.add (.read 2) (.literal 1)).Bounded [q, r, i, n, s] M
      (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, hiv, hone⟩
    simpa [Expr.run] using small_width hi
  have hpwidth : width ((i + 1) ^ (r - q)) ≤ 2 + M * M := by
    have h := width_pow_le (i + 1) (r - q)
    have hsiz : (i + 1).size ≤ M := (size_le_self (i + 1)).trans hi
    have hm := Nat.mul_le_mul (by omega : r - q ≤ M) hsiz
    omega
  have hp : (Expr.power (.add (.read 2) (.literal 1))
      (.sub (.read 1) (.read 0))).Bounded [q, r, i, n, s] M
      (intermediateWidthBound M) (registerReadBound M) := by
    refine ⟨?_, hadd, hsub, ?_, ?_⟩
    · simp only [Expr.run, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, powerRun_value]
      unfold intermediateWidthBound
      omega
    · simpa [Expr.run] using hi
    · simpa [Expr.run] using (by omega : r - q ≤ M)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, hqv, hrv⟩
    have hw : width (if q < r then (1 : ℕ) else 0) ≤ 2 := by
      by_cases hqr : q < r <;> simp [hqr, width]
    have hb : 2 ≤ intermediateWidthBound M := by unfold intermediateWidthBound; omega
    simpa [Expr.run] using hw.trans hb
  · refine ⟨?_, hsubone⟩
    simpa [Expr.run] using
      small_width (by have := Nat.mod_lt (r - q - 1) (by decide : 0 < 2); omega :
        (r - q - 1) % 2 ≤ M)
  · refine ⟨?_, hrv, hp⟩
    have hw := width_mul_le r ((i + 1) ^ (r - q))
    have hrw := width_le_of_le hr
    simp only [Expr.run, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, powerRun_value]
    unfold intermediateWidthBound
    omega

theorem entryProgram_bounds {M q r i n s : ℕ}
    (hM : 2 ≤ M) (hq : q ≤ M) (hr : r ≤ M) (hi : i + 1 ≤ M)
    (hn : n ≤ M) (hs : s ≤ M) :
    (entryProgram.run [q, r, i, n, s]).cost ≤ entryCostBound M ∧
      outputBits (entryProgram.run [q, r, i, n, s]).output ≤ entryOutputBound M := by
  let environment := [q, r, i, n, s]
  let condition : Expr := .less (.read 0) (.read 1)
  let sign : Expr := .odd (.sub (.sub (.read 1) (.read 0)) (.literal 1))
  let denominator : Expr := .mul (.read 1) (.power (.add (.read 2) (.literal 1))
    (.sub (.read 1) (.read 0)))
  let positive : Program := .emit sign (.literal 1) denominator
  let zero : Program := .emit (.literal 0) (.literal 0) (.literal 1)
  let E := generatorExpressionBudget M
  let B := intermediateWidthBound M
  have hE : 10 ≤ E := by unfold E generatorExpressionBudget expressionBudget; omega
  have hB : 1 ≤ B := by unfold B intermediateWidthBound; omega
  obtain ⟨hcondition, hsign, hdenominator⟩ := bounded_entryExpressions hM hq hr hi hn hs
  have hc : (condition.run environment).cost ≤ 3 * E := by
    have h := Expr.cost_le_nodes_budget environment M B (registerReadBound M) condition hcondition
    simpa [condition, Expr.nodes, E, B, generatorExpressionBudget] using h
  have hsc : (sign.run environment).cost ≤ 6 * E := by
    have h := Expr.cost_le_nodes_budget environment M B (registerReadBound M) sign hsign
    simpa [sign, Expr.nodes, E, B, generatorExpressionBudget] using h
  have hdc : (denominator.run environment).cost ≤ 9 * E := by
    have h := Expr.cost_le_nodes_budget environment M B (registerReadBound M) denominator hdenominator
    simpa [denominator, Expr.nodes, E, B, generatorExpressionBudget] using h
  have hdw : width (denominator.run environment).value ≤ B :=
    Expr.bounded_width hdenominator
  have hlc : ((Expr.literal 1).run environment).cost ≤ E := by
    change 3 ≤ E
    omega
  have hlw : width ((Expr.literal 1).run environment).value ≤ 2 := by
    simp [Expr.run, width]
  have hpc : (positive.run environment).cost ≤ 17 * E + B + 10 := by
    have h := emit_cost_le environment sign (.literal 1) denominator
      (6 * E) E (9 * E) 2 B hsc hlc hdc hlw hdw
    change (positive.run environment).cost ≤ _ at h
    omega
  have hpo : outputBits (positive.run environment).output ≤ B + 3 := by
    have h := emit_outputBits_le environment sign (.literal 1) denominator 2 B hlw hdw
    simpa [positive, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hzc : (zero.run environment).cost ≤ 17 * E + B + 10 := by
    simp only [zero, Program.run, Expr.run, RationalCode.bits, width, Nat.size_zero, Nat.size_one]
    omega
  have hzo : outputBits (zero.run environment).output ≤ B + 3 := by
    simp only [zero, Program.run, Expr.run, outputBits, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, RationalCode.bits, width, Nat.size_zero, Nat.size_one]
    omega
  have hcost := branch_cost_le environment condition positive zero (3 * E)
    (17 * E + B + 10) hc hpc hzc
  have houtput := branch_outputBits_le environment condition positive zero (B + 3) hpo hzo
  change (entryProgram.run environment).cost ≤ _ at hcost
  change outputBits (entryProgram.run environment).output ≤ _ at houtput
  constructor
  · unfold entryCostBound
    change (entryProgram.run environment).cost ≤ 20 * E + B + 20
    omega
  · exact houtput

def rowCostBound (M d : ℕ) : ℕ :=
  7 * generatorExpressionBudget M + 1 +
    d * (entryCostBound M + loopControlBound M + entryOutputBound M)

def rowOutputBound (M d : ℕ) : ℕ := d * entryOutputBound M

def variableCostBound (M d : ℕ) : ℕ :=
  7 * generatorExpressionBudget M + 1 +
    d * (rowCostBound M d + loopControlBound M + rowOutputBound M d)

def variableOutputBound (M d : ℕ) : ℕ := d * rowOutputBound M d

theorem rowProgram_bounds {M r i n s : ℕ}
    (hM : 2 ≤ M) (hr : r ≤ M) (hi : i + 1 ≤ M)
    (hn : n ≤ M) (hs : s ≤ M) (hd : 2 * n * s ^ 2 ≤ M) :
    (rowProgram.run [r, i, n, s]).cost ≤ rowCostBound M (2 * n * s ^ 2) ∧
      outputBits (rowProgram.run [r, i, n, s]).output ≤
        rowOutputBound M (2 * n * s ^ 2) := by
  have henv : ∀ a ∈ [r, i, n, s], a ≤ M := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hv : ((dimensionExpr 2 3).run [r, i, n, s]).value = 2 * n * s ^ 2 := by
    simp [dimensionExpr, Expr.run]
  have hc := dimensionExpr_cost_le (environment := [r, i, n, s])
    (nr := 2) (sr := 3) hM (by simp) henv (by omega) (by omega) rfl rfl hn hs
  have hb : ∀ q < ((dimensionExpr 2 3).run [r, i, n, s]).value,
      (entryProgram.run (q :: [r, i, n, s])).cost ≤ entryCostBound M ∧
      outputBits (entryProgram.run (q :: [r, i, n, s])).output ≤ entryOutputBound M := by
    intro q hq
    rw [hv] at hq
    exact entryProgram_bounds hM (by omega) hr hi hn hs
  constructor
  · have h := loop_cost_le [r, i, n, s] (dimensionExpr 2 3) entryProgram M
      (7 * generatorExpressionBudget M) (entryCostBound M) (entryOutputBound M)
      (by rw [hv]; exact hd) hc hb
    simpa only [rowProgram, rowCostBound, hv] using h
  · have h := loop_outputBits_le [r, i, n, s] (dimensionExpr 2 3) entryProgram
      (entryOutputBound M) (fun q hq => (hb q hq).2)
    simpa only [rowProgram, rowOutputBound, hv] using h

theorem variableProgram_bounds {M i n s : ℕ}
    (hM : 2 ≤ M) (hi : i + 1 ≤ M)
    (hn : n ≤ M) (hs : s ≤ M) (hd : 2 * n * s ^ 2 ≤ M) :
    (variableProgram.run [i, n, s]).cost ≤ variableCostBound M (2 * n * s ^ 2) ∧
      outputBits (variableProgram.run [i, n, s]).output ≤
        variableOutputBound M (2 * n * s ^ 2) := by
  have henv : ∀ a ∈ [i, n, s], a ≤ M := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hv : ((dimensionExpr 1 2).run [i, n, s]).value = 2 * n * s ^ 2 := by
    simp [dimensionExpr, Expr.run]
  have hc := dimensionExpr_cost_le (environment := [i, n, s])
    (nr := 1) (sr := 2) hM (by simp) henv (by omega) (by omega) rfl rfl hn hs
  have hb : ∀ r < ((dimensionExpr 1 2).run [i, n, s]).value,
      (rowProgram.run (r :: [i, n, s])).cost ≤ rowCostBound M (2 * n * s ^ 2) ∧
      outputBits (rowProgram.run (r :: [i, n, s])).output ≤
        rowOutputBound M (2 * n * s ^ 2) := by
    intro r hr
    rw [hv] at hr
    exact rowProgram_bounds hM (by omega) hi hn hs hd
  constructor
  · have h := loop_cost_le [i, n, s] (dimensionExpr 1 2) rowProgram M
      (7 * generatorExpressionBudget M) (rowCostBound M (2 * n * s ^ 2))
      (rowOutputBound M (2 * n * s ^ 2)) (by rw [hv]; exact hd) hc hb
    simpa only [variableProgram, variableCostBound, hv] using h
  · have h := loop_outputBits_le [i, n, s] (dimensionExpr 1 2) rowProgram
      (rowOutputBound M (2 * n * s ^ 2)) (fun r hr => (hb r hr).2)
    simpa only [variableProgram, variableOutputBound, hv] using h

def generatorCostBound (n s : ℕ) : ℕ :=
  let d := 2 * n * s ^ 2
  let M := n + s + d + 3
  2 * (M + 1) + 7 * generatorExpressionBudget M + 15 +
    (registerReadBound M + 1 +
      n * (variableCostBound M d + loopControlBound M + variableOutputBound M d)) + 1

theorem generate_cost_le (n s : ℕ) : (generate n s).cost ≤ generatorCostBound n s := by
  let d := 2 * n * s ^ 2
  let M := n + s + d + 3
  let E := generatorExpressionBudget M
  let B := intermediateWidthBound M
  let R := registerReadBound M
  let C := R + 1 + n * (variableCostBound M d + loopControlBound M + variableOutputBound M d)
  have hM : 2 ≤ M := by unfold M; omega
  have hn : n ≤ M := by unfold M; omega
  have hs : s ≤ M := by unfold M; omega
  have hd : d ≤ M := by unfold M; omega
  have hB : 4 ≤ B := by unfold B intermediateWidthBound; omega
  have henv : ∀ a ∈ [n, s], a ≤ M := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  have hnr := Expr.bounded_read (environment := [n, s]) (index := 0)
    (by simp) (by omega) henv
  have hsr := Expr.bounded_read (environment := [n, s]) (index := 1)
    (by simp) (by omega) henv
  have h1 := Expr.bounded_literal (environment := [n, s]) (a := 1) (by omega : 1 ≤ M)
  have hwif (a : ℕ) : width (if a = 1 then 1 else 0) ≤ 2 := by
    split <;> decide
  have hnt : (Expr.equal (.read 0) (.literal 1)).Bounded [n, s] M B R := by
    refine ⟨?_, hnr, h1⟩
    have h := (hwif n).trans (by omega : 2 ≤ B)
    simpa [Expr.run] using h
  have hst : (Expr.equal (.read 1) (.literal 1)).Bounded [n, s] M B R := by
    refine ⟨?_, hsr, h1⟩
    have h := (hwif s).trans (by omega : 2 ≤ B)
    simpa [Expr.run] using h
  let test : Expr := .mul (.equal (.read 0) (.literal 1)) (.equal (.read 1) (.literal 1))
  have ht : test.Bounded [n, s] M B R := by
    refine ⟨?_, hnt, hst⟩
    have h := width_mul_le (if n = 1 then 1 else 0) (if s = 1 then 1 else 0)
    have hnv := hwif n
    have hsv := hwif s
    have hw : width ((if n = 1 then 1 else 0) * (if s = 1 then 1 else 0)) ≤ B := by omega
    simpa [test, Expr.run] using hw
  have htc : (test.run [n, s]).cost ≤ 7 * E := by
    have h := Expr.cost_le_nodes_budget [n, s] M B R test ht
    simpa [test, Expr.nodes, E, B, R, generatorExpressionBudget] using h
  have hloop : ((Program.loop (.read 0) variableProgram).run [n, s]).cost ≤ C := by
    have hc : ((Expr.read 0).run [n, s]).cost ≤ R := hnr.2
    have hb : ∀ i < ((Expr.read 0).run [n, s]).value,
        (variableProgram.run (i :: [n, s])).cost ≤ variableCostBound M d ∧
        outputBits (variableProgram.run (i :: [n, s])).output ≤ variableOutputBound M d := by
      intro i hi
      change i < n at hi
      exact variableProgram_bounds hM (by omega) hn hs hd
    have h := loop_cost_le [n, s] (.read 0) variableProgram M R
      (variableCostBound M d) (variableOutputBound M d) hn hc hb
    exact h
  have hexception : ((Program.emit (.literal 0) (.literal 1) (.literal 1)).run [n, s]).cost ≤ 15 + C := by
    simp only [Program.run, Expr.run, RationalCode.bits, width, Nat.size_zero, Nat.size_one]
    omega
  have hbranch := branch_cost_le [n, s] test
    (.emit (.literal 0) (.literal 1) (.literal 1)) (.loop (.read 0) variableProgram)
    (7 * E) (15 + C) htc hexception (by omega)
  change (generatorProgram.run [n, s]).cost ≤ _ at hbranch
  have hinput : listBits [n, s] ≤ 2 * (M + 1) := by
    have hnw := width_le_of_le hn
    have hsw := width_le_of_le hs
    simp only [listBits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  change listBits [n, s] + (generatorProgram.run [n, s]).cost ≤ _
  change _ ≤ 2 * (M + 1) + 7 * E + 15 + C + 1
  omega

end NCHitting

end OAI
