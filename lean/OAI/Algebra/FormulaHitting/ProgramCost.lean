import Mathlib.Data.Nat.Size
import OAI.Algebra.FormulaHitting.BitModel
import Lean.Elab.Tactic.Omega

namespace OAI

namespace NCHitting.BitModel

private theorem bitSize_le_self (a : ℕ) : a.size ≤ a := by
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

private theorem bitSize_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

private theorem bitSize_pow_le (a k : ℕ) : (a ^ k).size ≤ 1 + k * a.size := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (a ^ (k + 1)).size = (a ^ k * a).size := by rw [pow_succ]
      _ ≤ (a ^ k).size + a.size := bitSize_mul_le _ _
      _ ≤ 1 + (k + 1) * a.size := by rw [Nat.add_mul]; omega

def powerStepBound (M : ℕ) : ℕ :=
  8 * (M * M + 2) * (M + 1) + 4 * (M + 3) + 1

theorem width_le_of_le {a M : ℕ} (ha : a ≤ M) : width a ≤ M + 1 := by
  exact Nat.add_le_add_right (Nat.le_trans (bitSize_le_self a) ha) 1

theorem powerRun_cost_le {base k M : ℕ} (hb : base ≤ M) (hk : k ≤ M) :
    (powerRun base k).cost ≤ 2 + k * powerStepBound M := by
  induction k with
  | zero => simp [powerRun, width]
  | succ k ih =>
    have hk' : k ≤ M := by omega
    have hbase : base.size ≤ M := (bitSize_le_self base).trans hb
    have hpow : width (base ^ k) ≤ M * M + 2 := by
      have h := bitSize_pow_le base k
      have hm : k * base.size ≤ M * M := Nat.mul_le_mul hk' hbase
      unfold width
      omega
    have hwbase : width base ≤ M + 1 := width_le_of_le hb
    have hwk : width k ≤ M + 1 := width_le_of_le hk'
    have hmul : mulCost (base ^ k) base ≤ 8 * (M * M + 2) * (M + 1) := by
      unfold mulCost
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 hpow) hwbase
    have hadd : addCost k 1 ≤ 4 * (M + 3) := by
      unfold addCost
      have : width 1 = 2 := rfl
      rw [this]
      exact Nat.mul_le_mul_left 4 (by omega)
    have hstep : mulCost (base ^ k) base + addCost k 1 + 1 ≤ powerStepBound M := by
      unfold powerStepBound
      omega
    simp only [powerRun, powerRun_value]
    calc
      (powerRun base k).cost + mulCost (base ^ k) base + addCost k 1 + 1
          ≤ (2 + k * powerStepBound M) + powerStepBound M := by
        have hprevious := ih hk'
        omega
      _ = 2 + (k + 1) * powerStepBound M := by rw [Nat.add_mul]; omega

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, f y ≤ C := by
      intro y hy
      exact h y (by simp [hy])
    have ht := ih hxs
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
    omega

theorem outputBits_append (xs ys : List RationalCode) :
    outputBits (xs ++ ys) = outputBits xs + outputBits ys := by
  simp [outputBits]

theorem outputBits_flatMap {α : Type*} (xs : List α) (f : α → List RationalCode) :
    outputBits (xs.flatMap f) = (xs.map fun x => outputBits (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [outputBits_append, ih]

def loopControlBound (M : ℕ) : ℕ := M + 1 + 4 * (M + 3) + 1

theorem loop_control_le {index M : ℕ} (hi : index ≤ M) :
    width index + addCost index 1 + 1 ≤ loopControlBound M := by
  have hw := width_le_of_le hi
  have h1 : width 1 = 2 := rfl
  unfold addCost loopControlBound
  rw [h1]
  omega

theorem loop_cost_le (environment : List ℕ) (bound : Expr) (body : Program)
    (M B C O : ℕ)
    (hvalue : (bound.run environment).value ≤ M)
    (hbound : (bound.run environment).cost ≤ B)
    (hbody : ∀ index < (bound.run environment).value,
      (body.run (index :: environment)).cost ≤ C ∧
      outputBits (body.run (index :: environment)).output ≤ O) :
    ((Program.loop bound body).run environment).cost ≤
      B + 1 + (bound.run environment).value * (C + loopControlBound M + O) := by
  simp only [Program.run, List.map_map, Function.comp_def]
  have hsum := sum_map_le_length_mul
    (List.range (bound.run environment).value)
    (fun index => (body.run (index :: environment)).cost +
      (width index + addCost index 1 + 1) +
      outputBits (body.run (index :: environment)).output)
    (C + loopControlBound M + O) (by
      intro index hindex
      have hi : index < (bound.run environment).value := List.mem_range.mp hindex
      obtain ⟨hc, ho⟩ := hbody index hi
      have hcontrol := loop_control_le (M := M) (by omega : index ≤ M)
      omega)
  simp only [List.length_range] at hsum
  omega

theorem loop_outputBits_le (environment : List ℕ) (bound : Expr) (body : Program)
    (O : ℕ)
    (hbody : ∀ index < (bound.run environment).value,
      outputBits (body.run (index :: environment)).output ≤ O) :
    outputBits ((Program.loop bound body).run environment).output ≤
      (bound.run environment).value * O := by
  simp only [Program.run, List.flatMap_map]
  rw [outputBits_flatMap]
  have hsum := sum_map_le_length_mul
    (List.range (bound.run environment).value)
    (fun index => outputBits (body.run (index :: environment)).output) O (by
      intro index hindex
      exact hbody index (List.mem_range.mp hindex))
  simpa only [List.length_range] using hsum

def expressionBudget (M B R : ℕ) : ℕ :=
  R + 8 * B * B + 8 * B + (2 + M * powerStepBound M) + 10

def Expr.nodes : Expr → ℕ
  | .literal _ | .read _ => 1
  | .add a b | .sub a b | .mul a b | .power a b | .less a b | .equal a b =>
      a.nodes + b.nodes + 1
  | .odd a => a.nodes + 1

def Expr.Bounded (environment : List ℕ) (M B R : ℕ) : Expr → Prop
  | .literal n => width n ≤ B ∧ True
  | .read index =>
      width ((Expr.read index).run environment).value ≤ B ∧
        ((Expr.read index).run environment).cost ≤ R
  | .add a b => width ((Expr.add a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R
  | .sub a b => width ((Expr.sub a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R
  | .mul a b => width ((Expr.mul a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R
  | .less a b => width ((Expr.less a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R
  | .equal a b => width ((Expr.equal a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R
  | .power a b => width ((Expr.power a b).run environment).value ≤ B ∧
      a.Bounded environment M B R ∧ b.Bounded environment M B R ∧
        (a.run environment).value ≤ M ∧ (b.run environment).value ≤ M
  | .odd a => width ((Expr.odd a).run environment).value ≤ B ∧
      a.Bounded environment M B R

theorem Expr.bounded_width {environment : List ℕ} {M B R : ℕ} {e : Expr}
    (h : e.Bounded environment M B R) : width (e.run environment).value ≤ B := by
  cases e <;> exact h.1

private theorem addCost_le_budget {a b M B R : ℕ}
    (ha : width a ≤ B) (hb : width b ≤ B) :
    addCost a b + 1 ≤ expressionBudget M B R := by
  unfold addCost expressionBudget
  omega

private theorem mulCost_le_budget {a b M B R : ℕ}
    (ha : width a ≤ B) (hb : width b ≤ B) :
    mulCost a b + 1 ≤ expressionBudget M B R := by
  have hm : 8 * width a * width b ≤ 8 * B * B :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 8 ha) hb
  unfold mulCost expressionBudget
  omega

private theorem compareCost_le_budget {a b M B R : ℕ}
    (ha : width a ≤ B) (hb : width b ≤ B) :
    compareCost a b + 1 ≤ expressionBudget M B R := by
  unfold compareCost expressionBudget
  omega

theorem Expr.cost_le_nodes_budget (environment : List ℕ) (M B R : ℕ) (e : Expr) :
    e.Bounded environment M B R →
      (e.run environment).cost ≤ e.nodes * expressionBudget M B R := by
  induction e with
  | literal n =>
    intro h
    have hw := h.1
    simp only [Expr.run, Expr.nodes, Nat.one_mul]
    unfold expressionBudget
    omega
  | read index =>
    intro h
    have hr := h.2
    simp only [Expr.nodes, Nat.one_mul]
    unfold expressionBudget
    omega
  | add a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hc := addCost_le_budget (M := M) (R := R) (Expr.bounded_width ha) (Expr.bounded_width hb)
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | sub a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hc := addCost_le_budget (M := M) (R := R) (Expr.bounded_width ha) (Expr.bounded_width hb)
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | mul a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hc := mulCost_le_budget (M := M) (R := R) (Expr.bounded_width ha) (Expr.bounded_width hb)
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | power a b iha ihb =>
    intro h
    obtain ⟨ha, hb, hav, hbv⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hp := powerRun_cost_le hav hbv
    have hm := Nat.mul_le_mul_right (powerStepBound M) hbv
    have hc : (powerRun (a.run environment).value (b.run environment).value).cost + 1 ≤
        expressionBudget M B R := by unfold expressionBudget; omega
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | less a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hc := compareCost_le_budget (M := M) (R := R) (Expr.bounded_width ha) (Expr.bounded_width hb)
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | equal a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h.2
    have hca := iha ha
    have hcb := ihb hb
    have hc := compareCost_le_budget (M := M) (R := R) (Expr.bounded_width ha) (Expr.bounded_width hb)
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega
  | odd a iha =>
    intro h
    have hca := iha h.2
    have hc : 2 ≤ expressionBudget M B R := by unfold expressionBudget; omega
    simp only [Expr.run, Expr.nodes, Nat.add_mul, Nat.one_mul]
    omega

theorem width_mul_le (a b : ℕ) : width (a * b) ≤ width a + width b := by
  have h := bitSize_mul_le a b
  unfold width
  omega

theorem width_pow_le (a k : ℕ) : width (a ^ k) ≤ 2 + k * a.size := by
  have h := bitSize_pow_le a k
  unfold width
  omega

def registerReadBound (M : ℕ) : ℕ := 5 * (M + 1) + 6

def intermediateWidthBound (M : ℕ) : ℕ := M * M + 4 * M + 10

theorem small_width {a M : ℕ} (ha : a ≤ M) : width a ≤ intermediateWidthBound M := by
  have h := width_le_of_le ha
  unfold intermediateWidthBound
  omega

theorem Expr.bounded_literal {environment : List ℕ} {a M : ℕ} (ha : a ≤ M) :
    (Expr.literal a).Bounded environment M (intermediateWidthBound M) (registerReadBound M) := by
  exact ⟨small_width ha, trivial⟩

theorem Expr.bounded_read {environment : List ℕ} {M index : ℕ}
    (hlen : environment.length ≤ 5) (hindex : index ≤ 4)
    (henv : ∀ a ∈ environment, a ≤ M) :
    (Expr.read index).Bounded environment M
      (intermediateWidthBound M) (registerReadBound M) := by
  have hvalue : environment[index]?.getD 0 ≤ M := by
    cases h : environment[index]? with
    | none => simp
    | some a => simpa [h] using henv a (List.mem_of_getElem? h)
  refine ⟨small_width hvalue, ?_⟩
  have hiwidth := width_le_of_le hindex
  have hprefix : (environment.take (index + 1)).length ≤ 5 := by
    simp only [List.length_take]
    exact (Nat.min_le_right _ _).trans hlen
  have hsum := sum_map_le_length_mul (environment.take (index + 1)) width (M + 1) (by
    intro a ha
    exact width_le_of_le (henv a (List.mem_of_mem_take ha)))
  have hm := Nat.mul_le_mul_right (M + 1) hprefix
  change width index + listBits (environment.take (index + 1)) + 1 ≤ registerReadBound M
  unfold listBits registerReadBound
  omega

theorem emit_cost_le (environment : List ℕ) (sign numerator denominator : Expr)
    (S N D A B : ℕ)
    (hs : (sign.run environment).cost ≤ S)
    (hn : (numerator.run environment).cost ≤ N)
    (hd : (denominator.run environment).cost ≤ D)
    (ha : width (numerator.run environment).value ≤ A)
    (hb : width (denominator.run environment).value ≤ B) :
    ((Program.emit sign numerator denominator).run environment).cost ≤
      S + N + D + (1 + A + B) + 2 := by
  simp only [Program.run, RationalCode.bits]
  omega

theorem emit_outputBits_le (environment : List ℕ) (sign numerator denominator : Expr)
    (A B : ℕ)
    (ha : width (numerator.run environment).value ≤ A)
    (hb : width (denominator.run environment).value ≤ B) :
    outputBits ((Program.emit sign numerator denominator).run environment).output ≤
      1 + A + B := by
  simp only [Program.run, outputBits, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, RationalCode.bits]
  omega

theorem branch_cost_le (environment : List ℕ) (test : Expr) (yes no : Program)
    (T C : ℕ) (ht : (test.run environment).cost ≤ T)
    (hy : (yes.run environment).cost ≤ C) (hn : (no.run environment).cost ≤ C) :
    ((Program.branch test yes no).run environment).cost ≤ T + C + 1 := by
  simp only [Program.run]
  split <;> omega

theorem branch_outputBits_le (environment : List ℕ) (test : Expr) (yes no : Program)
    (O : ℕ) (hy : outputBits (yes.run environment).output ≤ O)
    (hn : outputBits (no.run environment).output ≤ O) :
    outputBits ((Program.branch test yes no).run environment).output ≤ O := by
  simp only [Program.run]
  split <;> assumption

end NCHitting.BitModel

end OAI
