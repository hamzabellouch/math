import OAI.Combinatorics.ParityLifts.PolynomialLists

namespace OAI

namespace ParityWL.Complexity

lemma list_fold_map_context {α β γ : Type} (f : α × γ → β) (xs : List α)
    (bs : List β) (c : γ) :
    xs.foldl (fun s a => (f (a, s.2) :: s.1, s.2)) (bs, c) =
      ((xs.map (fun a => f (a, c))).reverse ++ bs, c) := by
  induction xs generalizing bs with
  | nil => simp
  | cons a xs ih => simp [ih, List.append_assoc]

def PolyProgram.mapWith {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α × γ → β} (P : PolyProgram (α × γ) β f) :
    PolyProgram (List α × γ) (List β) (fun x => x.1.map (fun a => f (a, x.2))) := by
  let a := PolyProgram.fst α (List β × γ)
  let bs := (PolyProgram.snd α (List β × γ)).comp (PolyProgram.fst (List β) γ)
  let c := (PolyProgram.snd α (List β × γ)).comp (PolyProgram.snd (List β) γ)
  let stepP := ((((a.pair c).comp P).pair bs).comp (PolyProgram.cons β)).pair c
  have hg (xs : List α) (s : List β × γ) :
      (treeEncode (xs.foldl (fun s a => (f (a, s.2) :: s.1, s.2)) s)).size ≤
        (P.coefficient + 4) * ((treeEncode (xs, s)).size + 1) ^ (P.degree + 1) := by
    rcases s with ⟨bs, c⟩
    rw [list_fold_map_context]
    let X := (treeEncode (xs, (bs, c))).size + 1
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hxpow : X ≤ X ^ (P.degree + 1) := by
      simpa using Nat.pow_le_pow_right hx (show 1 ≤ P.degree + 1 by omega)
    have hpow : 1 ≤ X ^ P.degree := Nat.one_le_pow _ _ hx
    have hsmall : (treeEncode bs).size + (treeEncode c).size + 1 ≤ X := by
      simp only [X, treeEncode_pair, DataTree.size]; omega
    have hlen : xs.length ≤ X := by
      have h := treeEncode_list_length xs
      simp only [X, treeEncode_pair, DataTree.size]; omega
    have hsum : ((xs.map (fun a => f (a, c))).map
        (fun a => (treeEncode a).size + 1)).sum ≤
        (P.coefficient + 1) * X ^ (P.degree + 1) := by
      rw [List.map_map]
      have h := list_sum_map_le xs
        (fun a => (treeEncode (f (a, c))).size + 1)
        ((P.coefficient + 1) * X ^ P.degree) (by
          intro a ha
          have hs := (P.program.run (a, c)).bounds.2.1
          have ht := P.bound (a, c)
          have ha := treeEncode_of_mem ha
          have hm : (treeEncode (a, c)).size + 1 ≤ X := by
            simp only [X, treeEncode_pair, DataTree.size]; omega
          have hp := Nat.mul_le_mul_left P.coefficient (Nat.pow_le_pow_left hm P.degree)
          nlinarith)
      calc
        _ ≤ xs.length * ((P.coefficient + 1) * X ^ P.degree) := h
        _ ≤ X * ((P.coefficient + 1) * X ^ P.degree) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    have he := treeEncode_append_size (xs.map (fun a => f (a, c))).reverse bs
    rw [treeEncode_reverse_size] at he
    have ht := treeEncode_list_size (xs.map (fun a => f (a, c)))
    simp only [treeEncode_pair, DataTree.size]
    change _ ≤ (P.coefficient + 4) * X ^ (P.degree + 1)
    nlinarith
  let F := stepP.foldlBounded (P.coefficient + 4) (P.degree + 1) hg
  let init := (PolyProgram.fst (List α) γ).pair
    ((PolyProgram.const ([] : List β)).pair (PolyProgram.snd (List α) γ))
  refine (init.comp F |>.comp (PolyProgram.fst (List β) γ) |>.comp
    (PolyProgram.reverse β)).congr ?_
  intro x
  change (x.1.foldl (fun s a => (f (a, s.2) :: s.1, s.2)) ([], x.2)).1.reverse = _
  simp [list_fold_map_context]

def PolyProgram.any {α : Type} [TreeCodec α] {p : α → Bool}
    (P : PolyProgram α Bool p) : PolyProgram (List α) Bool (fun xs => xs.any p) := by
  let stepP := ((PolyProgram.snd α Bool).pair ((PolyProgram.fst α Bool).comp P)).comp PolyProgram.or
  have hg (xs : List α) (b : Bool) :
      (treeEncode (xs.foldl (fun b a => b || p a) b)).size ≤
        3 * ((treeEncode (xs, b)).size + 1) ^ 0 := by
    cases xs.foldl (fun b a => b || p a) b <;> simp [DataTree.size]
  let F := stepP.foldlBounded 3 0 hg
  refine (((PolyProgram.id (List α)).pair (PolyProgram.const false)).comp F).congr ?_
  intro xs
  change xs.foldl (fun b a => b || p a) false = xs.any p
  have he (xs : List α) (b : Bool) : xs.foldl (fun b a => b || p a) b = (b || xs.any p) := by
    induction xs generalizing b with
    | nil => simp
    | cons a xs ih => simp [ih, Bool.or_assoc]
  simp [he]

def PolyProgram.all {α : Type} [TreeCodec α] {p : α → Bool}
    (P : PolyProgram α Bool p) : PolyProgram (List α) Bool (fun xs => xs.all p) := by
  refine ((P.comp PolyProgram.not).any.comp PolyProgram.not).congr ?_
  intro xs
  simp [Function.comp_def, List.all_eq_not_any_not]

end ParityWL.Complexity

namespace ParityWL.Complexity

def numTree : ℕ → DataTree
  | 0 => .nil
  | n + 1 => .node .nil (numTree n)

@[simp] lemma numTree_size (n : ℕ) : (numTree n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numTree, DataTree.size, ih]; omega

lemma numTree_injective : Function.Injective numTree := by
  intro n m h
  have := congrArg DataTree.size h
  simp only [numTree_size] at this
  omega

instance : TreeCodec ℕ := ⟨numTree, numTree_injective⟩
instance {n : ℕ} : TreeCodec (Fin n) :=
  ⟨fun i => numTree i.val, fun _ _ h => Fin.ext (numTree_injective h)⟩

@[simp] lemma treeEncode_nat (n : ℕ) : treeEncode n = numTree n := rfl
@[simp] lemma treeEncode_fin {n : ℕ} (i : Fin n) : treeEncode i = numTree i.val := rfl

instance {n : ℕ} {α : Type} [TreeCodec α] : TreeCodec (Fin n → α) where
  encode := fun f => treeEncode (List.ofFn f)
  injective := by
    intro f g h
    have he : List.ofFn f = List.ofFn g := TreeCodec.injective h
    exact List.ofFn_inj.mp he

@[simp] lemma treeEncode_fn_zero {α : Type} [TreeCodec α] (f : Fin 0 → α) :
    treeEncode f = .nil := by change treeEncode (List.ofFn f) = _; simp

@[simp] lemma treeEncode_fn_succ {n : ℕ} {α : Type} [TreeCodec α] (f : Fin (n+1) → α) :
    treeEncode f = .node (treeEncode (f 0)) (treeEncode (fun i : Fin n => f i.succ)) := by
  change treeEncode (List.ofFn f) = _
  rw [List.ofFn_succ]
  rfl

lemma treeEncode_fn_size {n : ℕ} {α : Type} [TreeCodec α] (f : Fin n → α) :
    (treeEncode f).size = 1 + ∑ i, ((treeEncode (f i)).size + 1) := by
  induction n with
  | zero => simp [DataTree.size]
  | succ n ih =>
    rw [treeEncode_fn_succ]
    simp only [DataTree.size, ih, Fin.sum_univ_succ]
    omega

def TExpr.nth (i : ℕ) (e : TExpr) : TExpr :=
  match i with
  | 0 => e.left
  | j + 1 => nth j e.right

lemma TExpr.nth_eval {n : ℕ} {α : Type} [TreeCodec α] (i : Fin n) (e : TExpr)
    (x : DataTree) (f : Fin n → α) (h : e.eval x = treeEncode f) :
    (e.nth i.val).eval x = treeEncode (f i) := by
  induction n generalizing e with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [nth, eval, h, DataTree.child]
    · apply ih i e.right (fun j => f j.succ)
      simp [eval, h, DataTree.child]

def TExpr.caseFin : (n : ℕ) → TExpr → (Fin n → TExpr) → TExpr → TExpr
  | 0, _, _, d => d
  | n + 1, e, f, d => .cond e (f 0) (caseFin n e.right (fun i => f i.succ) d)

lemma TExpr.caseFin_eval {n : ℕ} (i : Fin n) (e : TExpr) (f : Fin n → TExpr)
    (d : TExpr) (x : DataTree) (h : e.eval x = numTree i.val) :
    (caseFin n e f d).eval x = (f i).eval x := by
  induction n generalizing e with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simp [caseFin, eval, h, numTree]
    · intro h
      simp only [caseFin, eval, h, Fin.val_succ, numTree, reduceCtorEq, ↓reduceIte]
      apply ih i e.right (fun j => f j.succ)
      simp [eval, h, numTree, DataTree.child]

def TExpr.tuple : (n : ℕ) → (Fin n → TExpr) → TExpr
  | 0, _ => .nil
  | n + 1, f => .pair (f 0) (tuple n (fun i => f i.succ))

lemma TExpr.tuple_eval {n : ℕ} {α : Type} [TreeCodec α] (f : Fin n → TExpr)
    (x : DataTree) (g : Fin n → α) (h : ∀ i, (f i).eval x = treeEncode (g i)) :
    (tuple n f).eval x = treeEncode g := by
  induction n with
  | zero => simp [tuple, eval, treeEncode_fn_zero]
  | succ n ih => simp [tuple, eval, h 0, ih _ (fun i => g i.succ) (fun i => h i.succ)]

end ParityWL.Complexity

end OAI
