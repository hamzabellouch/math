import OAI.Computability.PerfectCompleteness.Machines.CircuitBatchLemmas
import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

def exprTokens (wire : ι → Nat) : Expr ι → List Token
  | .input i => [.input (wire i)]
  | .const b => [.const b]
  | .not e => exprTokens wire e ++ [.not]
  | .and e f => exprTokens wire e ++ exprTokens wire f ++ [.and]
  | .or e f => exprTokens wire e ++ exprTokens wire f ++ [.or]

def forestTokens (wire : ι → Nat) (es : List (Expr ι)) : List Token :=
  es.flatMap (exprTokens wire)

@[simp] theorem exprTokens_length (wire : ι → Nat) (e : Expr ι) :
    (exprTokens wire e).length = e.size := by
  induction e <;> simp_all [exprTokens, Expr.size, Nat.add_assoc]

@[simp] theorem exprTokens_rename {κ : Type*} (f : ι → κ) (wire : κ → Nat) (e : Expr ι) :
    exprTokens wire (e.rename f) = exprTokens (fun i => wire (f i)) e := by
  induction e <;> simp_all [Expr.rename, exprTokens]

@[simp] theorem forestTokens_nil (wire : ι → Nat) :
    forestTokens wire ([] : List (Expr ι)) = [] := rfl

@[simp] theorem forestTokens_cons (wire : ι → Nat) (e : Expr ι) (es : List (Expr ι)) :
    forestTokens wire (e :: es) = exprTokens wire e ++ forestTokens wire es := rfl

@[simp] theorem forestTokens_length (wire : ι → Nat) (es : List (Expr ι)) :
    (forestTokens wire es).length = Batch.cost es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [forestTokens_cons, List.length_append, exprTokens_length,
      ih, Batch.cost_cons]

theorem compileTokens_append
    (start : Nat) (roots : List Nat) (first rest : List Token)
    (middle : Nat) (middleRoots : List Nat) (firstGates : List Gate)
    (finish : Nat) (finalRoots : List Nat) (lastGates : List Gate)
    (hfirst : compileTokens start roots first = some (middle, middleRoots, firstGates))
    (hrest : compileTokens middle middleRoots rest = some (finish, finalRoots, lastGates)) :
    compileTokens start roots (first ++ rest) =
      some (finish, finalRoots, firstGates ++ lastGates) := by
  induction first generalizing start roots middle middleRoots firstGates with
  | nil =>
    simp only [compileTokens, Option.some.injEq, Prod.mk.injEq] at hfirst
    rcases hfirst with ⟨rfl, rfl, rfl⟩
    simpa only [List.nil_append] using hrest
  | cons token tokens ih =>
    cases hg : token.takeGate roots with
    | none => simp [compileTokens, hg] at hfirst
    | some pair =>
      rcases pair with ⟨gate, remaining⟩
      cases ht : compileTokens (start + 1) (start :: remaining) tokens with
      | none => simp [compileTokens, hg, ht] at hfirst
      | some triple =>
        rcases triple with ⟨next, afterRoots, tailGates⟩
        simp [compileTokens, hg, ht] at hfirst
        rcases hfirst with ⟨rfl, rfl, rfl⟩
        have hi := ih (start + 1) (start :: remaining) next afterRoots tailGates ht hrest
        simp [List.cons_append, compileTokens, hg, hi]

theorem compile_exprTokens (wire : ι → Nat) (e : Expr ι)
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (exprTokens wire e) =
      some (start + e.size, e.root start :: roots, e.gates wire start) := by
  induction e generalizing start roots with
  | input i => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | const b => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | not e ih =>
    have hop : compileTokens (start + e.size) (e.root start :: roots) [.not] =
        some (start + e.size + 1, (start + e.size) :: roots, [.not (e.root start)]) := rfl
    have he := compileTokens_append start roots (exprTokens wire e) [.not]
      _ _ _ _ _ _ (ih start roots) hop
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_not, Nat.add_assoc] using he
  | and e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.and] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.and (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.and] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.and]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_and, Nat.add_assoc,
      List.append_assoc] using he
  | or e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.or] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.or (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.or] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.or]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_or, Nat.add_assoc,
      List.append_assoc] using he

theorem compile_forestTokens (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (forestTokens wire es) =
      some (start + Batch.cost es, (Batch.roots start es).reverse ++ roots,
        Batch.gates wire start es) := by
  induction es generalizing start roots with
  | nil => simp [forestTokens, compileTokens, Batch.cost, Batch.roots, Batch.gates]
  | cons e es ih =>
    have h := compileTokens_append start roots (exprTokens wire e) (forestTokens wire es)
      _ _ _ _ _ _ (compile_exprTokens wire e start roots)
      (ih (start + e.size) (e.root start :: roots))
    simpa only [forestTokens_cons, Batch.cost_cons, Batch.roots, Batch.gates,
      List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_assoc] using h

theorem exprTokens_lowered_ordered (wire : ι → Nat) (e : Expr ι) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (e.gates wire start) :=
  e.gates_ordered wire start hw

theorem forestTokens_lowered_ordered (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (Batch.gates wire start es) :=
  Batch.gates_ordered wire start es hw

theorem forestTokens_preserves_root_suffix (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    ∃ fresh : List Nat,
      compileTokens start roots (forestTokens wire es) =
        some (start + Batch.cost es, fresh ++ roots, Batch.gates wire start es) ∧
      fresh.length = es.length ∧
      ∀ r ∈ fresh, start ≤ r ∧ r < start + Batch.cost es := by
  refine ⟨(Batch.roots start es).reverse, compile_forestTokens wire es start roots, ?_, ?_⟩
  · simp only [List.length_reverse, Batch.roots_length]
  · intro r hr
    exact Batch.roots_bounds start es r (List.mem_reverse.mp hr)

theorem expr_inputBits (wire : ι → Nat) (e : Expr ι) (start : Nat) :
    PostfixModel.inputBits start (exprTokens wire e) =
      encodeWords [start, e.size] ++ tokenBits (exprTokens wire e) := by
  simp only [PostfixModel.inputBits, exprTokens_length]

theorem forest_inputBits (wire : ι → Nat) (es : List (Expr ι)) (start : Nat) :
    PostfixModel.inputBits start (forestTokens wire es) =
      encodeWords [start, Batch.cost es] ++ tokenBits (forestTokens wire es) := by
  simp only [PostfixModel.inputBits, forestTokens_length]

theorem forest_gateRecords_alignment (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    (compileTokens start roots (forestTokens wire es)).map
      (fun result => gateRecords start result.2.2) =
      some (gateRecords start (Batch.gates wire start es)) := by
  rw [compile_forestTokens]
  rfl

theorem tokenWords_length_le (tokens : List Token) :
    (tokenWords tokens).length ≤ 2 * tokens.length := by
  induction tokens with
  | nil => simp [tokenWords]
  | cons t ts ih =>
    have ht : t.words.length ≤ 2 := by
      cases t with
      | const b => cases b <;> decide
      | not => decide
      | and => decide
      | or => decide
      | input w => simp [Token.words]
    simp only [tokenWords, List.flatMap_cons, List.length_append] at ih ⊢
    simp only [List.length_cons]
    omega

private theorem exprTokens_member (wire : ι → Nat) (e : Expr ι) (t : Token)
    (h : t ∈ exprTokens wire e) :
    (∃ b, t = .const b) ∨ t = .not ∨ t = .and ∨ t = .or ∨
      ∃ i, t = .input (wire i) := by
  induction e with
  | input i =>
    have ht : t = .input (wire i) := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, ht⟩)))
  | const b =>
    have ht : t = .const b := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inl ⟨b, ht⟩
  | not e ih =>
    simp only [exprTokens, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ih h
    · exact Or.inr (Or.inl rfl)
  | and e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inl rfl))
  | or e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem expr_tokenWords_bounded (wire : ι → Nat) (e : Expr ι) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (exprTokens wire e)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  rcases exprTokens_member wire e t ht with ⟨b, rfl⟩ | rfl | rfl | rfl | ⟨i, rfl⟩
  · cases b <;> simp only [Token.words, List.mem_singleton] at hword <;> omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_cons, List.not_mem_nil, or_false] at hword
    have hi := hw i
    rcases hword with rfl | rfl <;> omega

theorem forest_tokenWords_bounded (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (forestTokens wire es)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  obtain ⟨e, he, htoken⟩ := List.mem_flatMap.mp ht
  exact expr_tokenWords_bounded wire e start hw word
    (List.mem_flatMap.mpr ⟨t, htoken, hword⟩)

theorem forest_tokenBits_length_le (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) :
    (tokenBits (forestTokens wire es)).length ≤
      2 * Batch.cost es * (max 5 start + 1) := by
  have hb := encodeWords_length_le (tokenWords (forestTokens wire es)) (max 5 start)
    (forest_tokenWords_bounded wire es start hw)
  have hc : (tokenWords (forestTokens wire es)).length ≤ 2 * Batch.cost es := by
    simpa only [forestTokens_length] using tokenWords_length_le (forestTokens wire es)
  exact hb.trans (Nat.mul_le_mul_right _ hc)

theorem forest_inputBits_length_le (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) :
    (PostfixModel.inputBits start (forestTokens wire es)).length ≤
      start + Batch.cost es + 2 + 2 * Batch.cost es * (max 5 start + 1) := by
  rw [forest_inputBits, List.length_append]
  have hb := forest_tokenBits_length_le wire es start hw
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixAlignment

end

end OAI
