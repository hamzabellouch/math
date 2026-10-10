import OAI.Combinatorics.ParityLifts.Simulation

namespace OAI

namespace ParityWL.Complexity
abbrev Literal (N : ℕ) := Fin N × Bool

structure Clause (N : ℕ) where
  literals : List (Literal N)
  width : literals.length ≤ 3

abbrev Formula (N : ℕ) := List (Clause N)

def Clause.Satisfied {N : ℕ} (C : Clause N) (a : Fin N → Bool) : Prop :=
  ∃ l ∈ C.literals, a l.1 = l.2

def Formula.Satisfied {N : ℕ} (F : Formula N) (a : Fin N → Bool) : Prop :=
  ∀ C ∈ F, C.Satisfied a

def Formula.Satisfiable {N : ℕ} (F : Formula N) : Prop :=
  ∃ a, F.Satisfied a

/-- Self-delimiting binary natural numbers, followed by the explicit formula.
The clause width is encoded even for an empty clause. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ false :: n.bits

def encodeClause {N : ℕ} (C : Clause N) : List Bool :=
  encodeNat C.literals.length ++ C.literals.flatMap (fun l => encodeNat l.1.val ++ [l.2])

def encodeFormula {N : ℕ} (F : Formula N) : List Bool :=
  encodeNat N ++ encodeNat F.length ++ F.flatMap encodeClause


end ParityWL.Complexity

namespace ParityWL.Complexity

@[simp] lemma treeEncode_ticks (n : ℕ) : treeEncode (List.replicate n false) = numTree n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, numTree, ih]

def PolyProgram.ticks : PolyProgram ℕ (List Bool) (fun n => List.replicate n false) :=
  .expr .input (by intro n; simp [TExpr.eval])

def PolyProgram.natSucc : PolyProgram ℕ ℕ Nat.succ :=
  .expr (.pair .nil .input) (by intro n; rfl)

def PolyProgram.natPred : PolyProgram ℕ ℕ Nat.pred :=
  .expr TExpr.input.right (by intro n; cases n <;> rfl)

def PolyProgram.natZero : PolyProgram ℕ Bool (fun n => decide (n=0)) :=
  .expr (.cond .input (.const (boolTree true)) .nil) (by intro n; cases n <;> rfl)

lemma list_foldl_succ (xs : List Bool) (n : ℕ) :
    xs.foldl (fun m _ => m+1) n = n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons b bs ih => simp [ih]; omega

def PolyProgram.length (α : Type) [TreeCodec α] : PolyProgram (List α) ℕ List.length := by
  let S := (PolyProgram.snd α ℕ).comp PolyProgram.natSucc
  have hg (a : α) (n : ℕ) : (treeEncode (n+1)).size ≤
      (treeEncode n).size + 2*((treeEncode a).size+1)^0 := by simp; omega
  let F := S.foldlGrowing 2 0 hg
  refine (((PolyProgram.id (List α)).pair (PolyProgram.const 0)).comp F).congr ?_
  intro xs
  change xs.foldl (fun n _ => n+1) 0 = xs.length
  have he (ys : List α) (n : ℕ) : ys.foldl (fun m _ => m+1) n = n+ys.length := by
    induction ys generalizing n with
    | nil => simp
    | cons a ys ih => simp [ih]; omega
  exact (he xs 0).trans (Nat.zero_add _)

def truePrefix : List Bool → ℕ
  | [] => 0
  | true :: xs => truePrefix xs + 1
  | false :: _ => 0

lemma truePrefix_foldr (xs : List Bool) :
    xs.foldr (fun b n => if b then n+1 else 0) 0 = truePrefix xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [truePrefix, ih]

lemma truePrefix_le (xs : List Bool) : truePrefix xs ≤ xs.length := by
  induction xs with
  | nil => simp [truePrefix]
  | cons b xs ih => cases b <;> simp [truePrefix, ih]

def PolyProgram.truePrefix : PolyProgram (List Bool) ℕ truePrefix := by
  let S := (PolyProgram.fst Bool ℕ).ite
    ((PolyProgram.snd Bool ℕ).comp PolyProgram.natSucc) (PolyProgram.const 0)
  have hg (b : Bool) (n : ℕ) : (treeEncode (if b then n+1 else 0)).size ≤
      (treeEncode n).size + 2*((treeEncode b).size+1)^0 := by
    cases b <;> simp
    omega
  let F := S.foldlGrowing 2 0 hg
  refine ((((PolyProgram.reverse Bool).pair (PolyProgram.const 0)).comp F)).congr ?_
  intro xs
  change xs.reverse.foldl (fun n b => if b then n+1 else 0) 0 = Complexity.truePrefix xs
  rw [List.foldl_reverse, truePrefix_foldr]

def listShift {α : Type} (x : List α × List α) : List α × List α :=
  match x.1 with
  | [] => x
  | a :: xs => (xs, a :: x.2)

lemma listShift_size {α : Type} [TreeCodec α] (x : List α × List α) :
    (treeEncode (listShift x)).size = (treeEncode x).size := by
  rcases x with ⟨xs, ys⟩
  cases xs <;> simp [listShift, DataTree.size]
  omega

def PolyProgram.listShift (α : Type) [TreeCodec α] :
    PolyProgram (List α × List α) (List α × List α) listShift :=
  .expr (.cond TExpr.input.left .input
    (.pair TExpr.input.left.right (.pair TExpr.input.left.left TExpr.input.right)))
    (by rintro ⟨xs, ys⟩; cases xs <;> rfl)

lemma fold_shift {α : Type} (n : ℕ) (xs ys : List α) :
    (List.replicate n false).foldl (fun s _ => listShift s) (xs,ys) =
      (xs.drop n, (xs.take n).reverse ++ ys) := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simpa [List.replicate_succ, listShift] using ih [] ys
    | cons a xs =>
      simpa only [List.replicate_succ, List.foldl_cons, listShift, List.take_succ_cons,
        List.drop_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih xs (a :: ys)

def PolyProgram.splitAt (α : Type) [TreeCodec α] :
    PolyProgram (ℕ × List α) (List α × List α) (fun x => (x.2.take x.1, x.2.drop x.1)) := by
  let S := (PolyProgram.snd Bool (List α × List α)).comp (PolyProgram.listShift α)
  have hg (b : Bool) (x : List α × List α) :
      (treeEncode (Complexity.listShift x)).size ≤ (treeEncode x).size + 0*((treeEncode b).size+1)^0 := by
    simpa only [Nat.zero_mul, Nat.add_zero] using le_of_eq (listShift_size x)
  let F := S.foldlGrowing 0 0 hg
  let I := ((PolyProgram.fst ℕ (List α)).comp PolyProgram.ticks).pair
    ((PolyProgram.snd ℕ (List α)).pair (PolyProgram.const ([] : List α)))
  let O := ((PolyProgram.snd (List α) (List α)).comp (PolyProgram.reverse α)).pair
    (PolyProgram.fst (List α) (List α))
  refine ((I.comp F).comp O).congr ?_
  rintro ⟨n,xs⟩
  change (((List.replicate n false).foldl _ (xs,[])).2.reverse,
    ((List.replicate n false).foldl _ (xs,[])).1) = _
  simp [fold_shift]

def readNatBits (xs : List Bool) : List Bool × List Bool :=
  let n := truePrefix xs
  ((xs.drop (n+1)).take n, (xs.drop (n+1)).drop n)

def PolyProgram.readNatBits : PolyProgram (List Bool) (List Bool × List Bool) readNatBits := by
  let fst := PolyProgram.fst ℕ (List Bool)
  let snd := PolyProgram.snd ℕ (List Bool)
  let skip := ((fst.comp PolyProgram.natSucc).pair snd).comp (PolyProgram.splitAt Bool)
  let P := fst.pair (skip.comp (PolyProgram.snd (List Bool) (List Bool)))
  exact ((PolyProgram.truePrefix.pair (PolyProgram.id (List Bool))).comp P).comp
    (PolyProgram.splitAt Bool)

lemma truePrefix_encodeNat (n : ℕ) (xs : List Bool) :
    truePrefix (encodeNat n ++ xs) = n.bits.length := by
  unfold encodeNat
  rw [List.append_assoc, List.cons_append]
  generalize n.bits.length = k
  induction k with
  | zero => simp [truePrefix]
  | succ k ih => simp [List.replicate_succ, truePrefix, ih]

lemma readNatBits_encode (n : ℕ) (xs : List Bool) :
    readNatBits (encodeNat n ++ xs) = (n.bits,xs) := by
  rw [readNatBits, truePrefix_encodeNat]
  simp [encodeNat, List.drop_append]

lemma readNatBits_sizes (xs : List Bool) :
    (readNatBits xs).1.length ≤ xs.length ∧ (readNatBits xs).2.length ≤ xs.length := by
  simp [readNatBits, List.length_take, List.length_drop]

end ParityWL.Complexity

namespace ParityWL.Complexity

abbrev BitLiteral := List Bool × Bool
abbrev BitClause := List BitLiteral

def readLiteral (xs : List Bool) : BitLiteral × List Bool :=
  let x := readNatBits xs
  ((x.1,x.2.headD false),x.2.tail)

def PolyProgram.readLiteral : PolyProgram (List Bool) (BitLiteral × List Bool) readLiteral := by
  let E : PolyProgram (List Bool × List Bool) (BitLiteral × List Bool)
      (fun x => ((x.1,x.2.headD false),x.2.tail)) := .expr
    (.pair (.pair TExpr.input.left (.cond TExpr.input.right .nil TExpr.input.right.left)) TExpr.input.right.right)
    (by rintro ⟨a,b⟩; cases b <;> rfl)
  exact PolyProgram.readNatBits.comp E

def readLiterals : ℕ → List Bool → BitClause × List Bool
  | 0, xs => ([], xs)
  | n+1, xs =>
    let x := readLiteral xs
    let y := readLiterals n x.2
    (x.1::y.1,y.2)

def PolyProgram.readLiterals : (n : ℕ) → PolyProgram (List Bool) (BitClause × List Bool) (readLiterals n)
  | 0 => .expr (.pair .nil .input) (by intro xs; rfl)
  | n+1 =>
    let P := (PolyProgram.fst BitLiteral (List Bool)).pair
      ((PolyProgram.snd BitLiteral (List Bool)).comp (PolyProgram.readLiterals n))
    let Q : PolyProgram (BitLiteral × (BitClause × List Bool)) (BitClause × List Bool)
        (fun x => (x.1 :: x.2.1, x.2.2)) :=
      .expr (.pair (.pair TExpr.input.left TExpr.input.right.left) TExpr.input.right.right)
        (by intro x; rfl)
    (PolyProgram.readLiteral.comp P).comp Q

def readWidth (xs : List Bool) : ℕ :=
  if xs = (1 : ℕ).bits then 1 else if xs = (2 : ℕ).bits then 2 else
    if xs = (3 : ℕ).bits then 3 else 0

lemma readWidth_le (xs : List Bool) : readWidth xs ≤ 3 := by unfold readWidth; split_ifs <;> omega

lemma readWidth_bits (n : ℕ) (hn : n≤3) : readWidth n.bits = n := by
  interval_cases n <;> decide

def readClause (xs : List Bool) : BitClause × List Bool :=
  let x := readNatBits xs
  readLiterals (readWidth x.1) x.2

noncomputable def PolyProgram.readClause : PolyProgram (List Bool) (BitClause × List Bool) readClause := by
  let P (n : ℕ) := ((PolyProgram.fst (List Bool) (List Bool)).pair
    (PolyProgram.const n.bits)).comp (PolyProgram.equal (List Bool))
  let Q (n : ℕ) := (PolyProgram.snd (List Bool) (List Bool)).comp (PolyProgram.readLiterals n)
  refine (PolyProgram.readNatBits.comp ((P 1).ite (Q 1) ((P 2).ite (Q 2) ((P 3).ite (Q 3) (Q 0))))).congr ?_
  intro xs
  simp only [Function.comp_def]
  change (if decide ((Complexity.readNatBits xs).1 = (1:ℕ).bits) then _ else _) = _
  simp only [Complexity.readClause, readWidth, decide_eq_true_eq]
  split_ifs <;> rfl

lemma readNatBits_remainder (xs : List Bool) :
    (readNatBits xs).2.length ≤ xs.length := (readNatBits_sizes xs).2

lemma readNatBits_consumes (xs : List Bool) (hx : xs ≠ []) :
    (readNatBits xs).2.length < xs.length := by
  have hp := List.length_pos_iff_ne_nil.mpr hx
  simp only [readNatBits, List.length_drop]
  omega

lemma readNatBits_account (xs : List Bool) :
    (readNatBits xs).1.length + (readNatBits xs).2.length ≤ xs.length := by
  simp only [readNatBits, List.length_take, List.length_drop]
  omega

lemma readLiteral_remainder (xs : List Bool) : (readLiteral xs).2.length ≤ xs.length := by
  have := readNatBits_remainder xs
  simpa only [readLiteral, List.length_tail] using (Nat.sub_le (readNatBits xs).2.length 1).trans this

lemma readLiteral_account (xs : List Bool) :
    (treeEncode (readLiteral xs).1).size + 4*(readLiteral xs).2.length ≤ 4*xs.length+8 := by
  have h := readNatBits_account xs
  have ht := treeEncode_bits_size (readNatBits xs).1
  have hb : (treeEncode ((readNatBits xs).2.headD false)).size ≤ 3 := by
    cases (readNatBits xs).2.headD false <;> simp [DataTree.size]
  simp only [readLiteral, treeEncode_pair, DataTree.size, List.length_tail]
  omega

lemma readLiterals_remainder (n : ℕ) (xs : List Bool) :
    (readLiterals n xs).2.length ≤ xs.length := by
  induction n generalizing xs with
  | zero => exact le_rfl
  | succ n ih => exact (ih (readLiteral xs).2).trans (readLiteral_remainder xs)

lemma readLiterals_account (n : ℕ) (xs : List Bool) :
    (treeEncode (readLiterals n xs).1).size + 4*(readLiterals n xs).2.length ≤
      4*xs.length+9*n+1 := by
  induction n generalizing xs with
  | zero => simp [readLiterals, DataTree.size]; omega
  | succ n ih =>
    have h := ih (readLiteral xs).2
    have h' := readLiteral_account xs
    simp only [readLiterals, treeEncode_cons, DataTree.size]
    omega

lemma readClause_consumes (xs : List Bool) (hx : xs≠[]) : (readClause xs).2.length < xs.length :=
  (readLiterals_remainder _ _).trans_lt (readNatBits_consumes xs hx)

lemma readClause_account (xs : List Bool) (hx : xs≠[]) :
    (treeEncode (readClause xs).1).size+1+40*(readClause xs).2.length ≤ 40*xs.length := by
  have h := readLiterals_account (readWidth (readNatBits xs).1) (readNatBits xs).2
  have h' := readLiterals_remainder (readWidth (readNatBits xs).1) (readNatBits xs).2
  have hn := readNatBits_consumes xs hx
  have hw := readWidth_le (readNatBits xs).1
  dsimp only [readClause]
  omega

lemma readLiteral_encode (n : ℕ) (b : Bool) (xs : List Bool) :
    readLiteral (encodeNat n ++ b::xs) = ((n.bits,b),xs) := by
  simp [readLiteral, readNatBits_encode]

lemma readLiterals_encode (xs : List (ℕ × Bool)) (ys : List Bool) :
    readLiterals xs.length (xs.flatMap (fun x => encodeNat x.1 ++ [x.2]) ++ ys) =
      (xs.map (fun x => (x.1.bits,x.2)),ys) := by
  induction xs generalizing ys with
  | nil => simp [readLiterals]
  | cons x xs ih => simp [readLiterals, List.append_assoc, readLiteral_encode, ih]

lemma readClause_encode {N : ℕ} (C : Clause N) (xs : List Bool) :
    readClause (encodeClause C ++ xs) =
      (C.literals.map (fun l => (l.1.val.bits,l.2)),xs) := by
  simp only [readClause, encodeClause, List.append_assoc, readNatBits_encode,
    readWidth_bits C.literals.length C.width]
  have ht := readLiterals_encode (C.literals.map (fun l => (l.1.val,l.2))) xs
  simpa only [List.length_map, List.flatMap_map, Function.comp_def, List.map_map] using ht

end ParityWL.Complexity

end OAI
