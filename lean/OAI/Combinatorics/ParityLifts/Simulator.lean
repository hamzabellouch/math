import OAI.Combinatorics.ParityLifts.DataPrograms

namespace OAI

namespace ParityWL.Complexity

abbrev TapePair (a : ℕ) := List (Fin (a + 3)) × List (Fin (a + 3))

def listCell {a : ℕ} (xs : List (Fin (a + 3))) (n : ℕ) : Fin (a + 3) :=
  xs[n]?.getD 0

@[simp] lemma listCell_nil {a : ℕ} (n : ℕ) : listCell ([] : List (Fin (a+3))) n = 0 := by
  simp [listCell]
@[simp] lemma listCell_cons_zero {a : ℕ} (c : Fin (a+3)) (xs : List (Fin (a+3))) :
    listCell (c :: xs) 0 = c := rfl
@[simp] lemma listCell_cons_succ {a : ℕ} (c : Fin (a+3)) (xs : List (Fin (a+3))) (n : ℕ) :
    listCell (c :: xs) (n+1) = listCell xs n := rfl
lemma listCell_tail {a : ℕ} (xs : List (Fin (a+3))) (n : ℕ) :
    listCell xs.tail n = listCell xs (n+1) := by cases xs <;> simp
lemma listCell_zero {a : ℕ} (xs : List (Fin (a+3))) :
    listCell xs 0 = xs.headD 0 := by cases xs <;> rfl

def TapePair.cell {a : ℕ} (x : TapePair a) : ℤ → Fin (a+3)
  | .ofNat n => listCell x.2 n
  | .negSucc n => listCell x.1 n

def TapePair.advance {a : ℕ} (x : TapePair a) (c : Fin (a+3)) : Move → TapePair a
  | .stay => (x.1, c :: x.2.tail)
  | .right => (c :: x.1, x.2.tail)
  | .left => (x.1.tail, x.1.headD 0 :: c :: x.2.tail)

lemma TapePair.advance_cell {a : ℕ} (x : TapePair a) (c : Fin (a+3)) (m : Move) (z : ℤ) :
    (x.advance c m).cell z = if z + m.offset = 0 then c else x.cell (z + m.offset) := by
  cases m with
  | stay =>
    change (x.advance c .stay).cell z = if z + 0 = 0 then c else x.cell (z + 0)
    simp only [add_zero]
    cases z with
    | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega : Int.ofNat (n+1) ≠ 0)]
        exact listCell_tail x.2 n
    | negSucc n =>
      rw [ite_eq_right (by simp only [Int.negSucc_eq]; omega : Int.negSucc n ≠ 0)]
      rfl
  | right =>
    change (x.advance c .right).cell z = if z + 1 = 0 then c else x.cell (z + 1)
    cases z with
    | ofNat n =>
      rw [show Int.ofNat n + 1 = Int.ofNat (n+1) by simp only [Int.ofNat_eq_natCast]; omega,
        ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega : Int.ofNat (n+1) ≠ 0)]
      exact listCell_tail x.2 n
    | negSucc n =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [show Int.negSucc (n+1) + 1 = Int.negSucc n by simp only [Int.negSucc_eq]; omega,
          ite_eq_right (by simp only [Int.negSucc_eq]; omega : Int.negSucc n ≠ 0)]
        rfl
  | left =>
    change (x.advance c .left).cell z = if z + -1 = 0 then c else x.cell (z + -1)
    cases z with
    | ofNat n =>
      cases n with
      | zero =>
        rw [ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega : Int.ofNat 0 + -1 ≠ 0)]
        exact (listCell_zero x.1).symm
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          rw [show Int.ofNat (n+1+1) + -1 = Int.ofNat (n+1) by simp only [Int.ofNat_eq_natCast]; omega,
            ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega : Int.ofNat (n+1) ≠ 0)]
          exact listCell_tail x.2 n
    | negSucc n =>
      rw [show Int.negSucc n + -1 = Int.negSucc (n+1) by simp only [Int.negSucc_eq]; omega,
        ite_eq_right (by simp only [Int.negSucc_eq]; omega : Int.negSucc (n+1) ≠ 0)]
      exact listCell_tail x.1 n

lemma TapePair.advance_length {a : ℕ} (x : TapePair a) (c : Fin (a+3)) (m : Move) :
    (x.advance c m).1.length + (x.advance c m).2.length ≤ x.1.length + x.2.length + 2 := by
  cases m <;> simp [advance, List.length_tail] <;> omega

end ParityWL.Complexity

namespace ParityWL.Complexity

abbrev SmallConfiguration (M : Machine) :=
  Fin (M.extraStates + 1) × (Fin (M.tapes + 1) → TapePair M.extraSymbols)

def smallStep (M : Machine) (x : SmallConfiguration M) : SmallConfiguration M :=
  match M.output x.1 with
  | some _ => x
  | none =>
    let a := M.transition x.1 (fun i => (x.2 i).2.headD 0)
    (a.1, fun i => (x.2 i).advance (a.2 i).1 (a.2 i).2)

def smallInitial (M : Machine) (xs : List Bool) : SmallConfiguration M :=
  (M.initial, fun i => ([], if i.val = 0 then xs.map (inputSymbol M) else []))

def SmallRepresents (M : Machine) (x : SmallConfiguration M) (y : Configuration M) : Prop :=
  y.state = x.1 ∧ ∀ i z, y.tape i z = (x.2 i).cell (z - y.head i)

lemma smallStep_represents (M : Machine) (x : SmallConfiguration M) (y : Configuration M)
    (h : SmallRepresents M x y) : SmallRepresents M (smallStep M x) (step M y) := by
  have hread : (fun i => y.tape i (y.head i)) = fun i => (x.2 i).2.headD 0 := by
    funext i
    rw [h.2 i, sub_self]
    exact listCell_zero _
  cases ho : M.output x.1 with
  | some b => simpa only [smallStep, step, h.1, ho] using h
  | none =>
    simp only [SmallRepresents, smallStep, step, h.1, ho, hread]
    refine ⟨trivial, fun i z => ?_⟩
    rw [TapePair.advance_cell]
    have he : z - (y.head i + ((M.transition x.1 (fun i => (x.2 i).2.headD 0)).2 i).2.offset) +
        ((M.transition x.1 (fun i => (x.2 i).2.headD 0)).2 i).2.offset = z - y.head i := by ring
    rw [he]
    by_cases hz : z = y.head i
    · simp [hz]
    · simp only [↓reduceIte, sub_eq_zero, hz]
      exact h.2 i z

lemma smallInitial_represents (M : Machine) (xs : List Bool) :
    SmallRepresents M (smallInitial M xs) (initialConfiguration M xs) := by
  refine ⟨rfl, ?_⟩
  intro i z
  simp only [initialConfiguration, smallInitial, sub_zero]
  by_cases hi : i.val = 0
  · simp only [hi, true_and, ↓reduceIte]
    cases z with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
      change (match xs[n]? with | some b => inputSymbol M b | none => 0) =
        listCell (xs.map (inputSymbol M)) n
      simp [listCell, List.getElem?_map]
      cases xs[n]? <;> rfl
    | negSucc n =>
      have hn : ¬ 0 ≤ Int.negSucc n := by simp [Int.negSucc_eq]; omega
      simp only [hn, ↓reduceIte, TapePair.cell, listCell_nil]
  · simp only [hi, false_and, ↓reduceIte]
    cases z <;> simp [TapePair.cell]

lemma smallRun_represents (M : Machine) (xs : List Bool) (s : ℕ) :
    SmallRepresents M ((smallStep M)^[s] (smallInitial M xs)) (run M xs s) := by
  induction s with
  | zero => exact smallInitial_represents M xs
  | succ s ih =>
    simpa only [run, Function.iterate_succ_apply'] using smallStep_represents M _ _ ih

lemma smallRun_output {M : Machine} {xs : List Bool} {s : ℕ} {b : Bool}
    (h : Emits M xs s b) : M.output ((smallStep M)^[s] (smallInitial M xs)).1 = some b := by
  rw [← (smallRun_represents M xs s).1]
  exact h

lemma smallRun_tape_length (M : Machine) (xs : List Bool) (s : ℕ) (i : Fin (M.tapes + 1)) :
    (((smallStep M)^[s] (smallInitial M xs)).2 i).1.length +
      (((smallStep M)^[s] (smallInitial M xs)).2 i).2.length ≤ xs.length + 2 * s := by
  induction s with
  | zero => simp [smallInitial]; split <;> simp
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    rw [smallStep]
    split
    · omega
    · have h := TapePair.advance_length
        (((smallStep M)^[s] (smallInitial M xs)).2 i)
        ((M.transition ((smallStep M)^[s] (smallInitial M xs)).1
          (fun j => (((smallStep M)^[s] (smallInitial M xs)).2 j).2.headD 0)).2 i).1
        ((M.transition ((smallStep M)^[s] (smallInitial M xs)).1
          (fun j => (((smallStep M)^[s] (smallInitial M xs)).2 j).2.headD 0)).2 i).2
      exact h.trans (by omega)

lemma treeEncode_symbol_list_size {a : ℕ} (xs : List (Fin (a+3))) :
    (treeEncode xs).size ≤ 1 + xs.length * (2 * a + 6) := by
  rw [treeEncode_list_size]
  have h := list_sum_map_le xs (fun x => (treeEncode x).size + 1) (2*a+6) (by
    intro x _
    simp [numTree_size]
    omega)
  omega

lemma smallRun_size (M : Machine) (xs : List Bool) (s : ℕ) :
    (treeEncode ((smallStep M)^[s] (smallInitial M xs))).size ≤
      (2 * M.extraStates + (M.tapes + 1) * (4 * M.extraSymbols + 16) + 4) *
        (xs.length + s + 1) := by
  let x := (smallStep M)^[s] (smallInitial M xs)
  have hstate : (treeEncode x.1).size ≤ 2 * M.extraStates + 1 := by
    simp only [treeEncode_fin, numTree_size]
    have := x.1.isLt
    omega
  have htape (i : Fin (M.tapes+1)) :
      (treeEncode (x.2 i)).size + 1 ≤ (4 * M.extraSymbols + 16) * (xs.length + s + 1) := by
    have h := smallRun_tape_length M xs s i
    have hl := treeEncode_symbol_list_size (x.2 i).1
    have hr := treeEncode_symbol_list_size (x.2 i).2
    change (x.2 i).1.length + (x.2 i).2.length ≤ xs.length + 2*s at h
    simp only [treeEncode_prod, DataTree.size]
    have hm := Nat.mul_le_mul_right (2 * M.extraSymbols + 6) h
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (M.tapes+1)))) => htape i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  change (treeEncode x).size ≤ _
  rw [treeEncode_prod]
  simp only [DataTree.size, treeEncode_fn_size]
  nlinarith

end ParityWL.Complexity

namespace ParityWL.Complexity

def TExpr.caseTuple : (n m : ℕ) → (Fin n → TExpr) →
    ((Fin n → Fin m) → TExpr) → TExpr → TExpr
  | 0, _, _, f, _ => f Fin.elim0
  | n+1, m, es, f, d => caseFin m (es 0)
    (fun a => caseTuple n m (fun i => es i.succ) (fun xs => f (Fin.cons a xs)) d) d

lemma TExpr.caseTuple_eval {n m : ℕ} (es : Fin n → TExpr)
    (f : (Fin n → Fin m) → TExpr) (d : TExpr) (x : DataTree) (v : Fin n → Fin m)
    (h : ∀ i, (es i).eval x = treeEncode (v i)) :
    (caseTuple n m es f d).eval x = (f v).eval x := by
  induction n with
  | zero =>
    have he : (Fin.elim0 : Fin 0 → Fin m) = v := funext (fun i => Fin.elim0 i)
    simp [caseTuple, he]
  | succ n ih =>
    rw [caseTuple, caseFin_eval (v 0) _ _ d x (h 0)]
    rw [ih (fun i => es i.succ) (fun xs => f (Fin.cons (v 0) xs)) (fun i => v i.succ)
      (fun i => h i.succ)]
    congr 2
    exact Fin.cons_self_tail v

def TExpr.tapeHead (e : TExpr) : TExpr :=
  .cond e.right (.const (treeEncode (0 : Fin 3))) e.right.left

def TExpr.tapeAdvance {a : ℕ} (e : TExpr) (c : Fin (a+3)) : Move → TExpr
  | .stay => .pair e.left (.pair (.const (treeEncode c)) e.right.right)
  | .right => .pair (.pair (.const (treeEncode c)) e.left) e.right.right
  | .left => .pair e.left.right
    (.pair (.cond e.left .nil e.left.left) (.pair (.const (treeEncode c)) e.right.right))

lemma TExpr.tapeHead_eval {a : ℕ} (e : TExpr) (x : DataTree) (t : TapePair a)
    (h : e.eval x = treeEncode t) :
    (tapeHead e).eval x = treeEncode (t.2.headD 0) := by
  rcases t with ⟨l, r⟩
  cases r <;> simp [tapeHead, eval, h, DataTree.child, numTree]

lemma TExpr.tapeAdvance_eval {a : ℕ} (e : TExpr) (x : DataTree) (t : TapePair a)
    (h : e.eval x = treeEncode t) (c : Fin (a+3)) (m : Move) :
    (tapeAdvance e c m).eval x = treeEncode (t.advance c m) := by
  rcases t with ⟨l, r⟩
  cases m <;> cases l <;> cases r <;>
    simp [tapeAdvance, eval, h, TapePair.advance, DataTree.child, numTree]

def TExpr.smallStep (M : Machine) (e : TExpr) : TExpr :=
  .caseFin (M.extraStates+1) e.left (fun q =>
    match M.output q with
    | some _ => e
    | none => .caseTuple (M.tapes+1) (M.extraSymbols+3)
      (fun i => tapeHead (e.right.nth i.val))
      (fun v =>
        let a := M.transition q v
        .pair (.const (treeEncode a.1))
          (.tuple (M.tapes+1) (fun i => tapeAdvance (e.right.nth i.val) (a.2 i).1 (a.2 i).2))) .nil) .nil

lemma TExpr.smallStep_eval (M : Machine) (e : TExpr) (x : DataTree)
    (c : SmallConfiguration M) (h : e.eval x = treeEncode c) :
    (smallStep M e).eval x = treeEncode (Complexity.smallStep M c) := by
  have hq : e.left.eval x = numTree c.1.val := by simp [eval, h, DataTree.child]
  rw [smallStep, caseFin_eval c.1 _ _ _ x hq]
  cases ho : M.output c.1 with
  | some b => simpa [ho, Complexity.smallStep] using h
  | none =>
    simp only [ho, Complexity.smallStep]
    have hv (i : Fin (M.tapes+1)) :
        (tapeHead (e.right.nth i.val)).eval x = treeEncode ((c.2 i).2.headD 0) := by
      exact tapeHead_eval _ _ _ (nth_eval i e.right x c.2 (by simp [eval, h, DataTree.child]))
    rw [caseTuple_eval _ _ _ x (fun i => (c.2 i).2.headD 0) hv]
    simp only [eval, treeEncode_pair]
    congr 1
    apply tuple_eval
    intro i
    exact tapeAdvance_eval _ _ _ (nth_eval i e.right x c.2 (by simp [eval, h, DataTree.child])) _ _

def TExpr.smallContinue (M : Machine) (e : TExpr) : TExpr :=
  .caseFin (M.extraStates+1) e.left
    (fun q => .const (boolTree (M.output q).isNone)) .nil

def TExpr.smallAnswer (M : Machine) (e : TExpr) : TExpr :=
  .caseFin (M.extraStates+1) e.left
    (fun q => .const (boolTree ((M.output q).getD false))) .nil

lemma TExpr.smallContinue_eval (M : Machine) (e : TExpr) (x : DataTree)
    (c : SmallConfiguration M) (h : e.eval x = treeEncode c) :
    (smallContinue M e).eval x = boolTree (M.output c.1).isNone := by
  apply caseFin_eval c.1 e.left _ .nil x
  simp [eval, h, DataTree.child]

lemma TExpr.smallAnswer_eval (M : Machine) (e : TExpr) (x : DataTree)
    (c : SmallConfiguration M) (h : e.eval x = treeEncode c) :
    (smallAnswer M e).eval x = boolTree ((M.output c.1).getD false) := by
  apply caseFin_eval c.1 e.left _ .nil x
  simp [eval, h, DataTree.child]

end ParityWL.Complexity

end OAI
