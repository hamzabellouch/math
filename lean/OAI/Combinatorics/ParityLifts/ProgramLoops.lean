import OAI.Combinatorics.ParityLifts.TreePrograms

namespace OAI

namespace ParityWL.Complexity

@[simp] lemma treeEncode_tree (t : DataTree) : treeEncode t = t := rfl

lemma TreeProgram.loop_wf {α : Type} [TreeCodec α] {f : α → α}
    (P : TreeProgram α α f) (I : α → Prop) (μ : α → ℕ) (C : ℕ)
    (hs : ∀ x, I x → (treeEncode x).size ≤ C * (μ x + 1))
    (hb : ∀ x, I x → (treeEncode x).child false ≠ .nil → P.time x ≤ C * (μ x + 1))
    (hn : ∀ x, I x → (treeEncode x).child false ≠ .nil → I (f x) ∧ μ (f x) < μ x)
    (x : α) (hx : I x) :
    ∃ y, I y ∧ (treeEncode y).child false = .nil ∧
      BEval (.loop P.code) (treeEncode x) ((2 * C + 1) * (μ x + 1) ^ 2) (treeEncode y) := by
  generalize he : μ x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hg : (treeEncode x).child false = .nil
    · refine ⟨x, hx, hg, (BEval.loop_stop P.code (treeEncode x) hg).mono ?_⟩
      rw [← he]
      have hsq : μ x + 1 ≤ (μ x + 1) ^ 2 := by nlinarith [Nat.zero_le (μ x ^ 2)]
      calc
        _ ≤ C * (μ x + 1) := hs x hx
        _ ≤ C * (μ x + 1) ^ 2 := Nat.mul_le_mul_left C hsq
        _ ≤ (2 * C + 1) * (μ x + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨hI, hμ⟩ := hn x hx hg
      obtain ⟨y, hy, hnil, hr⟩ := ih (μ (f x)) (by omega) (f x) hI rfl
      refine ⟨y, hy, hnil, (BEval.loop_next hg ((P.run x).mono (hb x hx hg)) hr).mono ?_⟩
      rw [← he]
      have hsq : (μ (f x) + 1) ^ 2 ≤ (μ x) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hmul := Nat.mul_le_mul_left (2 * C + 1) hsq
      nlinarith

abbrev EqualState := List (DataTree × DataTree) × Bool

def equalStep : EqualState → EqualState
  | ([], b) => ([], b)
  | ((.nil, .nil) :: xs, b) => (xs, b)
  | ((.node l r, .node l' r') :: xs, b) => ((l, l') :: (r, r') :: xs, b)
  | (_ :: _, _) => ([], false)

def equalExpr : TExpr :=
  let tasks := TExpr.input.left
  let flag := TExpr.input.right
  let x := tasks.left.left
  let y := tasks.left.right
  let pop := TExpr.pair tasks.right flag
  let fail := TExpr.pair .nil .nil
  let expand := TExpr.pair
    (.pair (.pair x.left y.left) (.pair (.pair x.right y.right) tasks.right)) flag
  .cond x (.cond y pop fail) (.cond y fail expand)

lemma equalExpr_eval (s : EqualState) : equalExpr.eval (treeEncode s) = treeEncode (equalStep s) := by
  rcases s with ⟨xs, b⟩
  cases xs with
  | nil => simp [equalExpr, TExpr.eval, DataTree.child, equalStep]
  | cons p xs =>
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [equalExpr, TExpr.eval, DataTree.child, equalStep]

def equalStepProgram : TreeProgram EqualState EqualState equalStep where
  code := equalExpr.compile
  time := fun x => equalExpr.cost * ((treeEncode x).size + 1)
  run := fun x => by simpa only [equalExpr_eval] using equalExpr.run (treeEncode x)

def equalMeasure (s : EqualState) : ℕ := (s.1.map (fun p => p.1.size + p.2.size)).sum

def equalGood (s : EqualState) : Prop := s.2 = true ∧ ∀ p ∈ s.1, p.1 = p.2

lemma equalStep_good (s : EqualState) : equalGood (equalStep s) ↔ equalGood s := by
  rcases s with ⟨xs, b⟩
  cases xs with
  | nil => rfl
  | cons p xs =>
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [equalStep, equalGood, and_assoc, and_comm]

lemma equalStep_decreases (s : EqualState) (hs : (treeEncode s).child false ≠ .nil) :
    equalMeasure (equalStep s) < equalMeasure s := by
  rcases s with ⟨xs, b⟩
  cases xs with
  | nil => simp [DataTree.child] at hs
  | cons p xs =>
    rcases p with ⟨x, y⟩
    cases x <;> cases y
    all_goals simp [equalStep, equalMeasure, DataTree.size]
    all_goals omega

lemma equalState_size (s : EqualState) : (treeEncode s).size ≤ 2 * equalMeasure s + 5 := by
  rcases s with ⟨xs, b⟩
  have hlist : (treeEncode xs).size ≤ 2 * (xs.map (fun p => p.1.size + p.2.size)).sum + 1 := by
    induction xs with
    | nil => simp [DataTree.size]
    | cons p xs ih =>
      rcases p with ⟨x, y⟩
      have hx := x.size_pos
      have hy := y.size_pos
      simp only [treeEncode_cons, DataTree.size, treeEncode_pair, treeEncode_tree,
        List.map_cons, List.sum_cons]
      omega
  change 1 + (treeEncode xs).size + (treeEncode b).size ≤
    2 * (xs.map (fun p => p.1.size + p.2.size)).sum + 5
  cases b <;> simp only [treeEncode_false, treeEncode_true, DataTree.size] <;> omega

def FCode.treeEqual : FCode :=
  .seq (.pair (.pair .id .nil) (.const (boolTree true)))
    (.seq (.loop equalStepProgram.code) .right)

lemma BEval.treeEqual (x y : DataTree) :
    BEval FCode.treeEqual (.node x y)
      (100 * (equalExpr.cost + 1) * ((DataTree.node x y).size + 1) ^ 2)
      (treeEncode (decide (x = y))) := by
  let C := 6 * (equalExpr.cost + 1)
  have hs (s : EqualState) : (treeEncode s).size ≤ C * (equalMeasure s + 1) := by
    have := equalState_size s
    change (treeEncode s).size ≤ 6 * (equalExpr.cost + 1) * (equalMeasure s + 1)
    nlinarith
  have hb (s : EqualState) : equalStepProgram.time s ≤ C * (equalMeasure s + 1) := by
    have := equalState_size s
    change equalExpr.cost * ((treeEncode s).size + 1) ≤
      6 * (equalExpr.cost + 1) * (equalMeasure s + 1)
    nlinarith
  obtain ⟨s, hi, he, hr⟩ := equalStepProgram.loop_wf
    (fun s => equalGood s ↔ x = y) equalMeasure C
    (fun s _ => hs s) (fun s _ _ => hb s)
    (fun s h hne => ⟨(equalStep_good s).trans h, equalStep_decreases s hne⟩)
    ([(x, y)], true) (by simp [equalGood])
  have hnil : s.1 = [] := by
    have henc : treeEncode s.1 = .nil := by simpa [DataTree.child] using he
    exact TreeCodec.injective (by simpa using henc)
  have hbool : s.2 = decide (x = y) := by
    simp only [equalGood, hnil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at hi
    cases h : s.2 <;> simp_all
  have hinit := (BEval.id (.node x y)).pair (BEval.nil (.node x y))
  have hini := hinit.pair (BEval.const (boolTree true) (.node x y))
  have ht := hr.seq (BEval.right (treeEncode s))
  have h := hini.seq (by simpa [boolTree] using ht)
  have hout := hr.bounds.2.1
  simpa [FCode.treeEqual, DataTree.child, hbool] using h.mono (show _ ≤
      100 * (equalExpr.cost + 1) * ((DataTree.node x y).size + 1) ^ 2 from by
    simp only [equalMeasure, C, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] at hout ⊢
    simp only [boolTree, ↓reduceIte, DataTree.size]
    simp only [treeEncode_prod, DataTree.size] at hout
    generalize equalExpr.cost = E at hout ⊢
    nlinarith only [hout, Nat.zero_le E, Nat.zero_le x.size, Nat.zero_le y.size,
      Nat.zero_le (E * (x.size + y.size + 1) ^ 2), Nat.zero_le (E * x.size),
      Nat.zero_le (E * y.size)])

noncomputable def TreeProgram.equal (α : Type) [TreeCodec α] [DecidableEq α] :
    TreeProgram (α × α) Bool (fun x => decide (x.1 = x.2)) := by
  classical
  exact {
    code := FCode.treeEqual
    time := fun x => 100 * (equalExpr.cost + 1) * ((treeEncode x).size + 1) ^ 2
    run := fun x => by
      have he : (treeEncode x.1 = treeEncode x.2) ↔ x.1 = x.2 :=
        ⟨fun h => TreeCodec.injective (α := α) h, congrArg treeEncode⟩
      simpa [he] using BEval.treeEqual (treeEncode x.1) (treeEncode x.2)
  }

end ParityWL.Complexity

end OAI
