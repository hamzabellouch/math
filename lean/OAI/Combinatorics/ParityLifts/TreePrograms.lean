import OAI.Combinatorics.ParityLifts.FunctionalCompile

namespace OAI

namespace ParityWL.Complexity

def FCode.const : DataTree → FCode
  | .nil => .nil
  | .node l r => .pair (const l) (const r)

lemma BEval.const (t x : DataTree) : BEval (FCode.const t) x
    (t.size * (x.size + 1)) t := by
  induction t with
  | nil => exact (BEval.nil x).mono (by simp [DataTree.size])
  | node l r hl hr =>
    exact (hl.pair hr).mono (by simp [DataTree.size]; nlinarith)

/-- Finite tree expressions are uniformly linear in the size of their argument;
no arithmetic or lookup oracle is concealed in an expression. -/
inductive TExpr where
  | input
  | const (t : DataTree)
  | child (right : Bool) (e : TExpr)
  | pair (left right : TExpr)
  | cond (test nilCase nodeCase : TExpr)

def TExpr.eval : TExpr → DataTree → DataTree
  | .input, x => x
  | .const t, _ => t
  | .child b e, x => (e.eval x).child b
  | .pair e f, x => .node (e.eval x) (f.eval x)
  | .cond p e f, x => if p.eval x = .nil then e.eval x else f.eval x

def TExpr.compile : TExpr → FCode
  | .input => .id
  | .const t => .const t
  | .child false e => .seq e.compile .left
  | .child true e => .seq e.compile .right
  | .pair e f => .pair e.compile f.compile
  | .cond p e f => .cond p.compile e.compile f.compile

def TExpr.cost : TExpr → ℕ
  | .input => 1
  | .const t => t.size
  | .child _ e => 2 * e.cost + 2
  | .pair e f => e.cost + f.cost + 1
  | .cond p e f => p.cost + e.cost + f.cost + 1

lemma TExpr.run (e : TExpr) (x : DataTree) :
    BEval e.compile x (e.cost * (x.size + 1)) (e.eval x) := by
  induction e with
  | input => exact (BEval.id x).mono (by simp [TExpr.cost])
  | const t => exact BEval.const t x
  | child b e ih =>
    have hx := ih.bounds.2.1
    cases b
    · exact (ih.seq (BEval.left (e.eval x))).mono (by simp only [TExpr.cost]; nlinarith)
    · exact (ih.seq (BEval.right (e.eval x))).mono (by simp only [TExpr.cost]; nlinarith)
  | pair e f ih₁ ih₂ =>
    exact (ih₁.pair ih₂).mono (by simp [TExpr.cost]; nlinarith)
  | cond p e f ihp ihe ihf =>
    by_cases hp : p.eval x = .nil
    · have h := BEval.nil_cond (g := f.compile) (hp ▸ ihp) ihe
      simp only [TExpr.eval, hp, ↓reduceIte]
      exact h.mono (by simp [TExpr.cost]; nlinarith)
    · have h := BEval.node_cond (f := e.compile) ihp hp ihf
      simp only [TExpr.eval, hp, ↓reduceIte]
      exact h.mono (by simp [TExpr.cost]; nlinarith)

abbrev TExpr.left (e : TExpr) : TExpr := .child false e
abbrev TExpr.right (e : TExpr) : TExpr := .child true e
abbrev TExpr.nil : TExpr := .const .nil

lemma BEval.loop_iterate (p : FCode) (f : DataTree → DataTree) (x : DataTree)
    (n B S : ℕ)
    (hb : ∀ j, j < n → BEval p (f^[j] x) B (f^[j + 1] x))
    (hs : ∀ j, j ≤ n → (f^[j] x).size ≤ S)
    (hc : ∀ j, j < n → (f^[j] x).child false ≠ .nil)
    (he : (f^[n] x).child false = .nil) :
    BEval (.loop p) x ((n + 1) * (B + S + 1)) (f^[n] x) := by
  induction n generalizing x with
  | zero =>
    simpa using (BEval.loop_stop p x (by simpa using he)).mono
      (show x.size ≤ (0 + 1) * (B + S + 1) from by
        have hx : x.size ≤ S := by simpa using hs 0 (by omega)
        omega)
  | succ n ih =>
    have ht := ih (f x)
      (fun j hj => by simpa [Function.iterate_succ_apply] using hb (j + 1) (by omega))
      (fun j hj => by simpa [Function.iterate_succ_apply] using hs (j + 1) (by omega))
      (fun j hj => by simpa [Function.iterate_succ_apply] using hc (j + 1) (by omega))
      (by simpa [Function.iterate_succ_apply] using he)
    have h₀ : BEval p x B (f x) := by simpa using hb 0 (by omega)
    have hn : x.child false ≠ .nil := by simpa using hc 0 (by omega)
    have h := BEval.loop_next hn h₀ ht
    simpa [Function.iterate_succ_apply] using h.mono
      (show B + (n + 1) * (B + S + 1) + 1 ≤ (n + 1 + 1) * (B + S + 1) by nlinarith)

end ParityWL.Complexity

namespace ParityWL.Complexity

class TreeCodec (α : Type) where
  encode : α → DataTree
  injective : Function.Injective encode

abbrev treeEncode {α : Type} [TreeCodec α] (a : α) : DataTree := TreeCodec.encode a

instance : TreeCodec DataTree := ⟨id, Function.injective_id⟩

def boolTree (b : Bool) : DataTree := if b then .node .nil .nil else .nil
instance : TreeCodec Bool where
  encode := boolTree
  injective := by intro a b h; cases a <;> cases b <;> simp_all [boolTree]

@[simp] lemma treeEncode_false : treeEncode false = .nil := rfl
@[simp] lemma treeEncode_true : treeEncode true = .node .nil .nil := rfl

instance {α β : Type} [TreeCodec α] [TreeCodec β] : TreeCodec (α × β) where
  encode := fun x => .node (treeEncode x.1) (treeEncode x.2)
  injective := by
    intro a b h
    have hl := congrArg (DataTree.child false) h
    have hr := congrArg (DataTree.child true) h
    simp only [DataTree.child, Bool.false_eq_true, ↓reduceIte] at hl
    simp only [DataTree.child, ↓reduceIte] at hr
    exact Prod.ext (TreeCodec.injective hl) (TreeCodec.injective hr)

@[simp] lemma treeEncode_pair {α β : Type} [TreeCodec α] [TreeCodec β] (a : α) (b : β) :
    treeEncode (a, b) = .node (treeEncode a) (treeEncode b) := rfl

@[simp] lemma treeEncode_prod {α β : Type} [TreeCodec α] [TreeCodec β] (x : α × β) :
    treeEncode x = .node (treeEncode x.1) (treeEncode x.2) := rfl

def DataTree.ofList : List DataTree → DataTree
  | [] => .nil
  | x :: xs => .node x (ofList xs)

lemma DataTree.ofList_injective : Function.Injective ofList := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [ofList]
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => cases h
    | cons y ys =>
      have hl := congrArg (DataTree.child false) h
      have hr := congrArg (DataTree.child true) h
      simp [ofList, child] at hl hr
      simp [hl, ih hr]

instance {α : Type} [TreeCodec α] : TreeCodec (List α) where
  encode := fun xs => DataTree.ofList (xs.map treeEncode)
  injective := by
    intro xs ys h
    exact List.map_injective_iff.mpr TreeCodec.injective (DataTree.ofList_injective h)

@[simp] lemma treeEncode_nil {α : Type} [TreeCodec α] : treeEncode ([] : List α) = .nil := rfl
@[simp] lemma treeEncode_cons {α : Type} [TreeCodec α] (x : α) (xs : List α) :
    treeEncode (x :: xs) = .node (treeEncode x) (treeEncode xs) := rfl

lemma treeEncode_list_size {α : Type} [TreeCodec α] (xs : List α) :
    (treeEncode xs).size = 1 + (xs.map (fun x => (treeEncode x).size + 1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [DataTree.size, ih]; omega

lemma treeEncode_bits (bs : List Bool) : treeEncode bs = DataTree.ofBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [DataTree.ofBits, ih]; rfl

/-- A verified program on a concrete tree encoding. `time` is a proved bound on
both work and intermediate storage, never an oracle interpretation of `code`. -/
structure TreeProgram (α β : Type) [TreeCodec α] [TreeCodec β] (f : α → β) where
  code : FCode
  time : α → ℕ
  run : ∀ x, BEval code (treeEncode x) (time x) (treeEncode (f x))

def TreeProgram.id (α : Type) [TreeCodec α] : TreeProgram α α id where
  code := .id
  time := fun x => (treeEncode x).size
  run := fun x => BEval.id (treeEncode x)

def TreeProgram.const {α β : Type} [TreeCodec α] [TreeCodec β] (b : β) :
    TreeProgram α β (fun _ => b) where
  code := .const (treeEncode b)
  time := fun x => (treeEncode b).size * ((treeEncode x).size + 1)
  run := fun x => BEval.const (treeEncode b) (treeEncode x)

def TreeProgram.fst (α β : Type) [TreeCodec α] [TreeCodec β] : TreeProgram (α × β) α Prod.fst where
  code := .left
  time := fun x => (treeEncode x).size
  run := fun x => by
    cases x with
    | mk a b => simpa [DataTree.child] using BEval.left (treeEncode (a, b))

def TreeProgram.snd (α β : Type) [TreeCodec α] [TreeCodec β] : TreeProgram (α × β) β Prod.snd where
  code := .right
  time := fun x => (treeEncode x).size
  run := fun x => by
    cases x with
    | mk a b => simpa [DataTree.child] using BEval.right (treeEncode (a, b))

def TreeProgram.comp {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : TreeProgram α β f) (Q : TreeProgram β γ g) :
    TreeProgram α γ (g ∘ f) where
  code := .seq P.code Q.code
  time := fun x => P.time x + Q.time (f x) + 1
  run := fun x => (P.run x).seq (Q.run (f x))

def TreeProgram.pair {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : α → γ} (P : TreeProgram α β f) (Q : TreeProgram α γ g) :
    TreeProgram α (β × γ) (fun x => (f x, g x)) where
  code := .pair P.code Q.code
  time := fun x => P.time x + Q.time x + 1
  run := fun x => (P.run x).pair (Q.run x)

def TreeProgram.ite {α β : Type} [TreeCodec α] [TreeCodec β]
    {p : α → Bool} {f g : α → β} (P : TreeProgram α Bool p)
    (F : TreeProgram α β f) (G : TreeProgram α β g) :
    TreeProgram α β (fun x => if p x then f x else g x) where
  code := .cond P.code G.code F.code
  time := fun x => P.time x + (if p x then F.time x else G.time x) + 1
  run := by
    intro x
    cases hp : p x
    · simpa [hp] using (BEval.nil_cond (g := F.code) (by simpa [hp] using P.run x) (G.run x))
    · simpa [hp] using (BEval.node_cond (f := G.code) (by simpa [hp] using P.run x)
        (show treeEncode true ≠ .nil by simp) (F.run x))

lemma BEval.loop_terminates (p : FCode) (f : DataTree → DataTree) (I : DataTree → Prop)
    (μ : DataTree → ℕ) (C : ℕ)
    (hs : ∀ x, I x → x.size ≤ C * (μ x + 1))
    (hb : ∀ x, I x → x.child false ≠ .nil → BEval p x (C * (μ x + 1)) (f x))
    (hn : ∀ x, I x → x.child false ≠ .nil → I (f x) ∧ μ (f x) < μ x)
    (x : DataTree) (hx : I x) :
    ∃ y, I y ∧ y.child false = .nil ∧
      BEval (.loop p) x ((2 * C + 1) * (μ x + 1) ^ 2) y := by
  generalize he : μ x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hg : x.child false = .nil
    · refine ⟨x, hx, hg, (BEval.loop_stop p x hg).mono ?_⟩
      have hsz := hs x hx
      have hsq : μ x + 1 ≤ (μ x + 1) ^ 2 := by nlinarith [Nat.zero_le (μ x ^ 2)]
      rw [← he]
      calc
        x.size ≤ C * (μ x + 1) := hsz
        _ ≤ C * (μ x + 1) ^ 2 := Nat.mul_le_mul_left C hsq
        _ ≤ (2 * C + 1) * (μ x + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨hI, hμ⟩ := hn x hx hg
      obtain ⟨y, hy, hnil, hr⟩ := ih (μ (f x)) (by omega) (f x) hI rfl
      refine ⟨y, hy, hnil, (BEval.loop_next hg (hb x hx hg) hr).mono ?_⟩
      have hsq : (μ (f x) + 1) ^ 2 ≤ (μ x) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [← he]
      have hmul := Nat.mul_le_mul_left (2 * C + 1) hsq
      nlinarith

end ParityWL.Complexity

namespace ParityWL.Complexity

def TreeProgram.congr {α β : Type} [TreeCodec α] [TreeCodec β]
    {f g : α → β} (P : TreeProgram α β f) (h : ∀ x, f x = g x) :
    TreeProgram α β g := by
  have : f = g := funext h
  subst g
  exact P

def FCode.foldBody (p : FCode) : FCode :=
  .pair (.seq .left .right) (.seq (.pair (.seq .left .left) .right) p)

def TreeProgram.foldWork {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) : List α → β → ℕ
  | [], b => (treeEncode (([] : List α), b)).size
  | a :: xs, b => 10 * ((treeEncode (a :: xs, b)).size + 1) + P.time (a, b) +
      P.foldWork xs (f (a, b)) + 1

lemma TreeProgram.foldBody_run {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) (a : α) (xs : List α) (b : β) :
    BEval P.code.foldBody (treeEncode (a :: xs, b))
      (10 * ((treeEncode (a :: xs, b)).size + 1) + P.time (a, b))
      (treeEncode (xs, f (a, b))) := by
  let s := treeEncode (a :: xs, b)
  have hl : s.child false = treeEncode (a :: xs) := rfl
  have hll : (s.child false).child false = treeEncode a := rfl
  have hlr : (s.child false).child true = treeEncode xs := rfl
  have hr : s.child true = treeEncode b := rfl
  have ht := (BEval.left s).seq (BEval.right (s.child false))
  have hh := ((BEval.left s).seq (BEval.left (s.child false))).pair (BEval.right s)
  have ha := (hh.seq (by simpa [hll, hr] using P.run (a, b)))
  have result := ht.pair ha
  simpa [FCode.foldBody, hlr, s, DataTree.child] using result.mono
    (show _ ≤ 10 * (s.size + 1) + P.time (a, b) by
      have := s.size_child false
      omega)

lemma TreeProgram.foldLoop_run {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) (xs : List α) (b : β) :
    BEval (.loop P.code.foldBody) (treeEncode (xs, b)) (P.foldWork xs b)
      (treeEncode (([] : List α), xs.foldl (fun c a => f (a, c)) b)) := by
  induction xs generalizing b with
  | nil => exact BEval.loop_stop _ _ rfl
  | cons a xs ih =>
    exact BEval.loop_next (by simp [DataTree.child]) (P.foldBody_run a xs b) (ih (f (a, b)))

def TreeProgram.foldl {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) :
    TreeProgram (List α × β) β (fun x => x.1.foldl (fun c a => f (a, c)) x.2) where
  code := .seq (.loop P.code.foldBody) .right
  time := fun x => P.foldWork x.1 x.2 +
    (treeEncode (([] : List α), x.1.foldl (fun c a => f (a, c)) x.2)).size + 1
  run := by
    intro x
    simpa [DataTree.child] using (P.foldLoop_run x.1 x.2).seq
      (BEval.right (treeEncode (([] : List α), x.1.foldl (fun c a => f (a, c)) x.2)))

lemma treeEncode_list_size_mono {α : Type} [TreeCodec α] {xs ys : List α} (h : xs.Sublist ys) :
    (treeEncode xs).size ≤ (treeEncode ys).size := by
  rw [treeEncode_list_size, treeEncode_list_size]
  exact Nat.add_le_add_left (List.Sublist.sum_le_sum (h.map _) (fun _ _ => Nat.zero_le _)) 1

lemma TreeProgram.foldWork_bound {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) (xs : List α) (b : β)
    (I : β → Prop) (B A : ℕ) (hb : I b)
    (hs : ∀ b, I b → (treeEncode b).size ≤ A)
    (ht : ∀ a ∈ xs, ∀ b, I b → P.time (a, b) ≤ B)
    (hi : ∀ a ∈ xs, ∀ b, I b → I (f (a, b))) :
    P.foldWork xs b ≤ (xs.length + 1) *
      (10 * ((treeEncode xs).size + A + 2) + B + 1) ∧
    I (xs.foldl (fun c a => f (a, c)) b) := by
  induction xs generalizing b with
  | nil =>
    constructor
    · simp only [foldWork, treeEncode_pair, DataTree.size, treeEncode_nil, List.length_nil]
      have := hs b hb
      omega
    · exact hb
  | cons a xs ih =>
    obtain ⟨hcost, hres⟩ := ih (f (a, b)) (hi a (by simp) b hb)
      (fun x hx c hc => ht x (by simp [hx]) c hc)
      (fun x hx c hc => hi x (by simp [hx]) c hc)
    constructor
    · have htime := ht a (by simp) b hb
      have hsize := hs b hb
      have hlist : (treeEncode xs).size ≤ (treeEncode (a :: xs)).size := by
        simp [DataTree.size]
      have hmul := Nat.mul_le_mul_left (xs.length + 1)
        (show 10 * ((treeEncode xs).size + A + 2) + B + 1 ≤
           10 * ((treeEncode (a :: xs)).size + A + 2) + B + 1 by omega)
      simp only [foldWork, List.length_cons, treeEncode_pair, DataTree.size]
      nlinarith
    · exact hres

end ParityWL.Complexity

end OAI
