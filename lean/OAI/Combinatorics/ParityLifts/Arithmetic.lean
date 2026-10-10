import OAI.Combinatorics.ParityLifts.Parser

namespace OAI

namespace ParityWL.Complexity

lemma fold_pred (n m : ℕ) : (List.replicate n false).foldl (fun a _ => a-1) m = m-n := by
  induction n generalizing m with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]; omega

lemma fold_succ (n m : ℕ) : (List.replicate n false).foldl (fun a _ => a+1) m = m+n := by
  simp

def PolyProgram.natAdd : PolyProgram (ℕ × ℕ) ℕ (fun x => x.1+x.2) := by
  let P := (PolyProgram.snd Bool ℕ).comp PolyProgram.natSucc
  have hg (b : Bool) (n : ℕ) : (treeEncode (n+1)).size ≤
      (treeEncode n).size+2*((treeEncode b).size+1)^0 := by simp; omega
  let F := P.foldlGrowing 2 0 hg
  exact ((((PolyProgram.fst ℕ ℕ).comp PolyProgram.ticks).pair (PolyProgram.snd ℕ ℕ)).comp F).congr
    (by intro x; simp [Nat.add_comm])

def PolyProgram.natSub : PolyProgram (ℕ × ℕ) ℕ (fun x => x.1-x.2) := by
  let P := (PolyProgram.snd Bool ℕ).comp PolyProgram.natPred
  have hg (b : Bool) (n : ℕ) : (treeEncode n.pred).size ≤
      (treeEncode n).size+0*((treeEncode b).size+1)^0 := by simp
  let F := P.foldlGrowing 0 0 hg
  exact ((((PolyProgram.snd ℕ ℕ).comp PolyProgram.ticks).pair (PolyProgram.fst ℕ ℕ)).comp F).congr
    (by intro x; exact fold_pred x.2 x.1)

def PolyProgram.natLe : PolyProgram (ℕ × ℕ) Bool (fun x => decide (x.1≤x.2)) :=
  (PolyProgram.natSub.comp PolyProgram.natZero).congr (by intro x; simp [Nat.sub_eq_zero_iff_le])

def PolyProgram.natMin : PolyProgram (ℕ × ℕ) ℕ (fun x => min x.1 x.2) :=
  PolyProgram.natLe.ite (PolyProgram.fst ℕ ℕ) (PolyProgram.snd ℕ ℕ) |>.congr
    (by intro x; simp [min_def])

def PolyProgram.drop (α : Type) [TreeCodec α] :
    PolyProgram (ℕ × List α) (List α) (fun x => x.2.drop x.1) :=
  (PolyProgram.splitAt α).comp (PolyProgram.snd (List α) (List α))

def PolyProgram.take (α : Type) [TreeCodec α] :
    PolyProgram (ℕ × List α) (List α) (fun x => x.2.take x.1) :=
  (PolyProgram.splitAt α).comp (PolyProgram.fst (List α) (List α))

def PolyProgram.getD (α : Type) [TreeCodec α] (a : α) :
    PolyProgram (ℕ × List α) α (fun x => x.2[x.1]?.getD a) :=
  ((PolyProgram.drop α).comp (PolyProgram.head α a)).congr (by intro x; simp)

def PolyProgram.evalFin (n : ℕ) (α : Type) [TreeCodec α] :
    PolyProgram (Fin n × (Fin n → α)) α (fun x => x.2 x.1) :=
  .expr (TExpr.caseFin n TExpr.input.left
    (fun i => TExpr.input.right.nth i.val) .nil) (by
      rintro ⟨i,f⟩
      rw [TExpr.caseFin_eval i _ _ _ _ (by rfl)]
      exact TExpr.nth_eval i _ _ f (by rfl))

def PolyProgram.finite {n : ℕ} {α : Type} [TreeCodec α] (f : Fin n → α) :
    PolyProgram (Fin n) α f :=
  .expr (TExpr.caseFin n .input (fun i => .const (treeEncode (f i))) .nil) (by
    intro i
    rw [TExpr.caseFin_eval i _ _ _ _ (by rfl)]
    rfl)

def rangeStep (s : ℕ × List ℕ) : ℕ × List ℕ := (s.1+1,s.1::s.2)

lemma fold_rangeStep (xs : List Bool) (s : ℕ × List ℕ) :
    xs.foldl (fun s _ => rangeStep s) s = (s.1+xs.length, (List.range' s.1 xs.length).reverse++s.2) := by
  induction xs generalizing s with
  | nil => simp
  | cons b xs ih =>
    change xs.foldl (fun s _ => rangeStep s) (rangeStep s) = _
    rw [ih]
    simp only [rangeStep, List.length_cons, List.range'_succ,
      List.reverse_cons, List.append_assoc, List.singleton_append]
    apply Prod.ext
    · omega
    · rfl

lemma treeEncode_range'_size (n m : ℕ) :
    (treeEncode (List.range' n m)).size ≤ 1+m*(2*(n+m)+2) := by
  rw [treeEncode_list_size]
  apply Nat.add_le_add_left
  have h := list_sum_map_le (List.range' n m) (fun a => (treeEncode a).size+1) (2*(n+m)+2) ?_
  · simpa using h
  intro a ha
  have hn := List.mem_range'.mp ha
  simp only [treeEncode_nat, numTree_size]
  omega

def PolyProgram.range : PolyProgram ℕ (List ℕ) List.range := by
  let P : PolyProgram (Bool × (ℕ × List ℕ)) (ℕ × List ℕ) (fun x => rangeStep x.2) :=
    .expr (.pair (.pair .nil TExpr.input.right.left)
      (.pair TExpr.input.right.left TExpr.input.right.right)) (by intro x; rfl)
  have hg (xs : List Bool) (s : ℕ × List ℕ) :
      (treeEncode (xs.foldl (fun s _ => rangeStep s) s)).size ≤
        4*((treeEncode (xs,s)).size+1)^2 := by
    rw [fold_rangeStep, treeEncode_prod, DataTree.size]
    have h := treeEncode_append_size (List.range' s.1 xs.length).reverse s.2
    rw [treeEncode_reverse_size] at h
    have hr := treeEncode_range'_size s.1 xs.length
    have hx := treeEncode_list_length xs
    simp only [treeEncode_prod, treeEncode_nat, numTree_size, DataTree.size]
    nlinarith
  let F := P.foldlBounded 4 2 hg
  refine (((PolyProgram.ticks.pair (PolyProgram.const (0,([]:List ℕ)))).comp F).comp
    (PolyProgram.snd ℕ (List ℕ)) |>.comp (PolyProgram.reverse ℕ)).congr ?_
  intro n
  change ((List.replicate n false).foldl (fun s _ => rangeStep s) (0,([]:List ℕ))).2.reverse = _
  simp [fold_rangeStep, List.range_eq_range']

end ParityWL.Complexity

namespace ParityWL.Complexity

def succBits (bs : List Bool) : List Bool :=
  List.replicate (truePrefix bs) false ++ true :: bs.drop (truePrefix bs+1)

@[simp] lemma succBits_nil : succBits [] = [true] := rfl
@[simp] lemma succBits_false (bs : List Bool) : succBits (false::bs) = true::bs := rfl
@[simp] lemma succBits_true (bs : List Bool) : succBits (true::bs) = false::succBits bs := by
  simp [succBits, truePrefix, List.replicate_succ, List.drop_succ_cons]

lemma succBits_bits (n : ℕ) : succBits n.bits = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    cases b with
    | false =>
      have hn' : n≠0 := by intro h; have := hn h; contradiction
      simp only [Nat.bit_false, Nat.bit0_bits n hn', succBits_false, Nat.bit1_bits]
    | true =>
      rw [Nat.bit_true, Nat.bit1_bits, succBits_true, ih]
      have he : 2*n+1+1=2*(n+1) := by omega
      rw [he, Nat.bit0_bits (n+1) (by omega)]

lemma succBits_size (bs : List Bool) : (treeEncode (succBits bs)).size ≤ (treeEncode bs).size+4 := by
  induction bs with
  | nil => simp [DataTree.size]
  | cons b bs ih =>
    cases b <;> simp only [succBits_false, succBits_true, treeEncode_cons, DataTree.size,
      treeEncode_false, treeEncode_true, DataTree.size] <;> omega

def PolyProgram.succBits : PolyProgram (List Bool) (List Bool) succBits := by
  let P := PolyProgram.truePrefix
  let pre :=  P.comp PolyProgram.ticks
  let suffix := (((P.comp PolyProgram.natSucc).pair (PolyProgram.id (List Bool))).comp
    (PolyProgram.drop Bool))
  let R := (((PolyProgram.const true).pair suffix).comp (PolyProgram.cons Bool))
  exact (pre.pair R).comp (PolyProgram.append Bool)

lemma fold_succBits (xs : List Bool) (n : ℕ) :
    xs.foldl (fun bs _ => succBits bs) n.bits = (n+xs.length).bits := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih => simp only [List.foldl_cons, succBits_bits, ih, List.length_cons]; congr 1; omega

def PolyProgram.natBits : PolyProgram ℕ (List Bool) Nat.bits := by
  let P := (PolyProgram.snd Bool (List Bool)).comp PolyProgram.succBits
  have hg (b : Bool) (bs : List Bool) : (treeEncode (Complexity.succBits bs)).size ≤
      (treeEncode bs).size+4*((treeEncode b).size+1)^0 := by simpa using succBits_size bs
  let F := P.foldlGrowing 4 0 hg
  refine ((PolyProgram.ticks.pair (PolyProgram.const ([]:List Bool))).comp F).congr ?_
  intro n
  change (List.replicate n false).foldl (fun bs _ => Complexity.succBits bs) (0:ℕ).bits = n.bits
  simpa only [Nat.zero_add, List.length_replicate] using fold_succBits (List.replicate n false) 0

def PolyProgram.encodeNat : PolyProgram ℕ (List Bool) encodeNat := by
  let B := PolyProgram.natBits
  let N := B.comp (PolyProgram.length Bool)
  let pre :=  (N.comp PolyProgram.ticks).comp ((PolyProgram.const (α:=Bool) true).map)
  let suffix := ((PolyProgram.const false).pair B).comp (PolyProgram.cons Bool)
  refine ((pre.pair suffix).comp (PolyProgram.append Bool)).congr ?_
  intro n
  simp [Complexity.encodeNat]

end ParityWL.Complexity

end OAI
