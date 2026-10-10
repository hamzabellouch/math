import OAI.Combinatorics.ContingencyTables.Sampling.GreedyTableMachine
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyRowComplexity

namespace OAI

/-! # Polynomial binary cost of the full greedy table constructor -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped Polynomial

private lemma listLE_trans {as bs cs : List ℕ}
    (hab : List.Forall₂ (·≤·) as bs) (hbc : List.Forall₂ (·≤·) bs cs) :
    List.Forall₂ (·≤·) as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact .nil
  | cons hab htail ih =>
    cases hbc with
    | cons hbc hrest => exact .cons (hab.trans hbc) (ih hrest)

private lemma weight_listLE {as bs : List ℕ} (h : List.Forall₂ (·≤·) as bs) :
    weight as≤4*weight bs := by
  induction h with
  | nil => simp
  | cons hab htail ih =>
    have hn := weight_nat_small hab
    simp only [weight_cons]
    omega

lemma listSplitRow_le (a : ℕ) (cs : List ℕ) :
    List.Forall₂ (·≤·) (listSplitRow a cs).2.1 cs ∧
    List.Forall₂ (·≤·) (listSplitRow a cs).2.2 cs := by
  induction cs generalizing a with
  | nil => exact ⟨.nil,.nil⟩
  | cons c cs ih =>
    exact ⟨.cons (min_le_right _ _) (ih (a-min a c)).1,
      .cons (Nat.sub_le _ _) (ih (a-min a c)).2⟩

private lemma tableFold_bounds (rs cs base : List ℕ) (rows : List (List ℕ))
    (hc : List.Forall₂ (·≤·) cs base) :
    List.Forall₂ (·≤·) (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).1 base ∧
    weight (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).2≤
      rs.length*(4*weight base+1)+weight rows := by
  induction rs generalizing cs rows with
  | nil => exact ⟨hc,by simp⟩
  | cons a rs ih =>
    have hr := listSplitRow_le a cs
    have hout := weight_listLE (listLE_trans hr.1 hc)
    have ht := ih (listSplitRow a cs).2.2 ((listSplitRow a cs).2.1::rows)
      (listLE_trans hr.2 hc)
    refine ⟨ht.1,?_⟩
    change weight (rs.foldl (fun z a => tableRow (a,z))
      ((listSplitRow a cs).2.2,(listSplitRow a cs).2.1::rows)).2≤_
    simp only [List.length_cons,weight_cons] at ht ⊢
    nlinarith [ht.2]

lemma polynomial_tableRow : PolynomialTime tableRowRealizer := by
  have hrow : PolynomialTime (composition
      (pair (first (A := ℕ) (B := TableAccumulator)) (composition second first))
      rowSplitRealizer) :=
    polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_rowSplit
  have hrows : PolynomialTime (composition
      (second (A := ℕ) (B := TableAccumulator)) second) :=
    polynomial_composition polynomial_second polynomial_second
  unfold tableRowRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_composition hrow polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition hrow polynomial_second) polynomial_first)
      hrows) polynomial_listCons))

lemma polynomial_tableFold : PolynomialTime (fold tableRowRealizer) := by
  apply polynomial_fold polynomial_tableRow (12*(X+1)^2)
  rintro rs ⟨cs,rows⟩ pre post he
  have hc : List.Forall₂ (·≤·) cs cs := by
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons le_rfl ih
  have ht := tableFold_bounds pre cs cs rows hc
  have hw := weight_listLE ht.1
  have hp := (list_length_le_weight pre).trans (weight_prefix he)
  let S := weight (rs,(cs,rows))
  have hrs : weight rs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hcs : weight cs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hrows : weight rows≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hpre : pre.length≤S := hp.trans hrs
  change weight (pre.foldl (fun z a => tableRow (a,z)) (cs,rows))≤_
  rw [←Prod.eta (pre.foldl (fun z a => tableRow (a,z)) (cs,rows)),weight_prod]
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤12*(S+1)^2
  have hm := Nat.mul_le_mul hpre (show 4*weight cs+1≤4*S+1 by omega)
  nlinarith [ht.2]

/-- The single fixed program has polynomial bit cost, uniformly in both
dimensions and all binary margin values. -/
theorem polynomial_table : PolynomialTime tableRealizer := by
  unfold tableRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_tableFold
  exact polynomial_pair polynomial_first
    (polynomial_pair polynomial_second (polynomial_constant []))

end ContingencyTables.GreedyFeasibleTable

end OAI
