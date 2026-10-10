import OAI.Computability.MeanPayoff.Stack

namespace OAI

section
namespace MeanPayoff.RegisterBits
@[simp] theorem install_self {K N : ℕ} (f : Fin K → Fin N) (s : Fin N → List Bool) :
    install f s (fun i => s (f i)) = s := by
  funext j
  unfold install
  split_ifs with h
  · exact congrArg s (Classical.choose_spec h)
  · rfl

def slots {K : ℕ} (i j : Fin K) : Fin 4 → Fin (K + 2)
  | 0 => i.castAdd 2
  | 1 => j.castAdd 2
  | 2 => ⟨K, by omega⟩
  | 3 => ⟨K + 1, by omega⟩

theorem slots_injective {K : ℕ} (i j : Fin K) (hij : i ≠ j) :
    Function.Injective (slots i j) := by
  intro a b hab
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  fin_cases a <;> fin_cases b <;> simp only [slots, Fin.ext_iff, Fin.val_castAdd] at hab ⊢ <;> omega

theorem renamed_start {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (s : Fin N → List Bool) (out : List Bool) :
    renamed P f s ⟨some P.start, (fun i => s (f i)), out⟩ =
      ⟨some (rename P f).start, s, out⟩ := by
  simp only [renamed, install_self]; rfl

theorem move_tree {K : ℕ} (i j : Fin K) (hij : i ≠ j) (s : Fin (K+2) → List Bool)
    (out : List Bool) (t : BinaryData.Data) (xs ys : List Bool)
    (h0 : s (i.castAdd 2) = BinaryData.encode t ++ xs)
    (h1 : s (j.castAdd 2) = ys)
    (h2 : s ⟨K, by omega⟩ = []) (h3 : s ⟨K+1, by omega⟩ = []) (bits : ℕ → Bool) :
    advance (rename BinaryData.Take.program (slots i j)) bits
      ⟨some (rename BinaryData.Take.program (slots i j)).start, s, out⟩
      (6 * (BinaryData.encode t).length + 3) =
    ⟨none, Function.update (Function.update s (i.castAdd 2) xs) (j.castAdd 2)
      (BinaryData.encode t ++ ys), out⟩ := by
  have hf := slots_injective i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hKi : K ≠ i.val := by have hi := i.isLt; omega
  have hKj : K ≠ j.val := by have hj := j.isLt; omega
  have h1i : K+1 ≠ i.val := by have hi := i.isLt; omega
  have h1j : K+1 ≠ j.val := by have hj := j.isLt; omega
  have hs : (fun a => s (slots i j a)) = ![BinaryData.encode t ++ xs, ys, [], []] := by
    funext a; fin_cases a <;> simpa only [slots, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (by assumption)
  rw [← renamed_start BinaryData.Take.program (slots i j) s out, hs, rename_advance _ _ hf]
  change renamed _ _ s (advance BinaryData.Take.program bits
    (BinaryData.Take.cfg .start (BinaryData.encode t ++ xs) ys [] [] out) _) = _
  rw [BinaryData.Take.takes]
  apply BinaryData.Take.config_ext
  · rfl
  · funext a
    change install (slots i j) s ![xs, BinaryData.encode t ++ ys, [], []] a = _
    by_cases ha : ∃ b, slots i j b = a
    · obtain ⟨b, rfl⟩ := ha
      rw [install_at _ hf]
      fin_cases b <;> simp [slots, h2, h3,
        Fin.ext_iff, hne, hKi, hKj, h1i, h1j]
    · rw [install_off _ _ _ _ (by simpa using ha)]
      have hi : a ≠ i.castAdd 2 := by intro h; exact ha ⟨0, h.symm⟩
      have hj : a ≠ j.castAdd 2 := by intro h; exact ha ⟨1, h.symm⟩
      simp [Function.update_of_ne hi, Function.update_of_ne hj]
  · rfl

theorem copy_tree {K : ℕ} (i j : Fin K) (hij : i ≠ j) (s : Fin (K+2) → List Bool)
    (out : List Bool) (t : BinaryData.Data) (xs ys : List Bool)
    (h0 : s (i.castAdd 2) = BinaryData.encode t ++ xs)
    (h1 : s (j.castAdd 2) = ys)
    (h2 : s ⟨K, by omega⟩ = []) (h3 : s ⟨K+1, by omega⟩ = []) (bits : ℕ → Bool) :
    advance (rename BinaryData.Copy.program (slots i j)) bits
      ⟨some (rename BinaryData.Copy.program (slots i j)).start, s, out⟩
      (7 * (BinaryData.encode t).length + 3) =
    ⟨none, Function.update s (j.castAdd 2) (BinaryData.encode t ++ ys), out⟩ := by
  have hf := slots_injective i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hKi : K ≠ i.val := by have hi := i.isLt; omega
  have hKj : K ≠ j.val := by have hj := j.isLt; omega
  have h1i : K+1 ≠ i.val := by have hi := i.isLt; omega
  have h1j : K+1 ≠ j.val := by have hj := j.isLt; omega
  have hs : (fun a => s (slots i j a)) = ![BinaryData.encode t ++ xs, ys, [], []] := by
    funext a; fin_cases a <;> simpa only [slots, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (by assumption)
  rw [← renamed_start BinaryData.Copy.program (slots i j) s out, hs, rename_advance _ _ hf]
  change renamed _ _ s (advance BinaryData.Copy.program bits
    (BinaryData.Copy.cfg .start (BinaryData.encode t ++ xs) ys [] [] out) _) = _
  rw [BinaryData.Copy.copies]
  apply BinaryData.Take.config_ext
  · rfl
  · funext a
    change install (slots i j) s ![BinaryData.encode t ++ xs, BinaryData.encode t ++ ys, [], []] a = _
    by_cases ha : ∃ b, slots i j b = a
    · obtain ⟨b, rfl⟩ := ha
      rw [install_at _ hf]
      fin_cases b <;> simp [slots, h0, h2, h3,
        Fin.ext_iff, hne, hKj, h1j]
    · rw [install_off _ _ _ _ (by simpa using ha)]
      have hj : a ≠ j.castAdd 2 := by intro h; exact ha ⟨1, h.symm⟩
      simp [Function.update_of_ne hj]
  · rfl
end MeanPayoff.RegisterBits
namespace MeanPayoff.ForestMachine
open BinaryData (Data)
open RegisterBits
open BinaryStack (applyOp)

inductive Instruction (K N : ℕ) where
  | nil (i : Fin K) (next : Fin N)
  | join (i : Fin K) (next : Fin N)
  | split (i : Fin K) (empty nil pair : Fin N)
  | move (i j : Fin K) (different : i ≠ j) (next : Fin N)
  | copy (i j : Fin K) (different : i ≠ j) (next : Fin N)
  | emit (b : Bool) (next : Fin N)
  | coin (zero one : Fin N)
  | halt

structure Program (K : ℕ) where
  nodes : ℕ
  start : Fin nodes
  code : Fin nodes → Instruction K nodes
structure Config {K : ℕ} (P : Program K) where
  control : Option (Fin P.nodes)
  store : Fin K → List Data
  output : List Bool

def encodeForest (xs : List Data) : List Bool := (xs.map BinaryData.encode).flatten
@[simp] theorem encodeForest_nil : encodeForest [] = [] := rfl
@[simp] theorem encodeForest_cons (x : Data) (xs : List Data) :
    encodeForest (x :: xs) = BinaryData.encode x ++ encodeForest xs := rfl

def bitStore {K : ℕ} (s : Fin K → List Data) : Fin (K+2) → List Bool :=
  fun i => if h : i.val < K then encodeForest (s ⟨i.val, h⟩) else []
@[simp] theorem bitStore_at {K : ℕ} (s : Fin K → List Data) (i : Fin K) :
    bitStore s (i.castAdd 2) = encodeForest (s i) := by simp [bitStore, i.isLt]
@[simp] theorem bitStore_scratch₀ {K : ℕ} (s : Fin K → List Data) :
    bitStore s ⟨K, by omega⟩ = [] := by simp [bitStore]
@[simp] theorem bitStore_scratch₁ {K : ℕ} (s : Fin K → List Data) :
    bitStore s ⟨K+1, by omega⟩ = [] := by simp [bitStore]

theorem bitStore_update {K : ℕ} (s : Fin K → List Data) (i : Fin K) (xs : List Data) :
    bitStore (Function.update s i xs) = Function.update (bitStore s) (i.castAdd 2) (encodeForest xs) := by
  funext j
  by_cases hj : j.val < K
  · have hj' : j = (⟨j.val, hj⟩ : Fin K).castAdd 2 := rfl
    rw [hj']
    simp only [bitStore_at, Function.update_apply]
    split_ifs with he hf hg <;> simp_all [Fin.ext_iff]
  · have hne : j ≠ i.castAdd 2 := by intro h; subst j; exact hj i.isLt
    simp [bitStore, hj, Function.update_of_ne hne]

def Valid {K : ℕ} (P : Program K) (c : Config P) : Prop :=
  match c.control with
  | none => True
  | some q => match P.code q with
    | .join i _ => 2 ≤ (c.store i).length
    | .move i _ _ _ | .copy i _ _ _ => c.store i ≠ []
    | _ => True

def step {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q => match P.code q with
    | .nil i r => ⟨some r, Function.update c.store i (.nil :: c.store i), c.output⟩
    | .join i r => ⟨some r, Function.update c.store i
        (match c.store i with | a :: b :: xs => .pair a b :: xs | xs => xs), c.output⟩
    | .split i e n p => match c.store i with
        | [] => ⟨some e, c.store, c.output⟩
        | .nil :: xs => ⟨some n, Function.update c.store i xs, c.output⟩
        | .pair a b :: xs => ⟨some p, Function.update c.store i (a :: b :: xs), c.output⟩
    | .move i j _ r => match c.store i with
        | [] => ⟨some r, c.store, c.output⟩
        | a :: xs => ⟨some r, Function.update (Function.update c.store i xs) j (a :: c.store j), c.output⟩
    | .copy i j _ r => match c.store i with
        | [] => ⟨some r, c.store, c.output⟩
        | a :: _ => ⟨some r, Function.update c.store j (a :: c.store j), c.output⟩
    | .emit b r => ⟨some r, c.store, c.output ++ [b]⟩
    | .coin z o => ⟨some (if bit then o else z), c.store, c.output⟩
    | .halt => ⟨none, c.store, c.output⟩

def skip (K : ℕ) : RegisterBits.Program (K+2) where
  states := 1
  start := 0
  read _ := ⟨K, by omega⟩
  transition _ _ _ := none

noncomputable def block {K N : ℕ} : Instruction K N → RegisterBits.Program (K+2)
  | .move i j _ _ => rename BinaryData.Take.program (slots i j)
  | .copy i j _ _ => rename BinaryData.Copy.program (slots i j)
  | _ => skip K

def read {K N : ℕ} : Instruction K N → Fin (K+2)
  | .nil i _ | .join i _ | .split i _ _ _ => i.castAdd 2
  | _ => ⟨K, by omega⟩

def branch {K N : ℕ} (op : Instruction K N) (top : Option Bool) (bit : Bool) : Option (Act N) :=
  match op with
  | .nil _ r => some ⟨r, .push false, none⟩
  | .join _ r => some ⟨r, .push true, none⟩
  | .split _ e n p => some ⟨match top with | none => e | some false => n | some true => p,
      .pop, none⟩
  | .move _ _ _ r | .copy _ _ _ r => some ⟨r, .keep, none⟩
  | .emit b r => some ⟨r, .keep, some b⟩
  | .coin z o => some ⟨if bit then o else z, .keep, none⟩
  | .halt => none

noncomputable abbrev flow {K : ℕ} (P : Program K) : Flow.Program (K+2) where
  nodes := P.nodes
  start := P.start
  block q := block (P.code q)
  read q := read (P.code q)
  next q := branch (P.code q)

noncomputable def compile {K : ℕ} (P : Program K) := Flow.compile (flow P)
noncomputable def embed {K : ℕ} (P : Program K) (c : Config P) : RegisterBits.Config (compile P) :=
  ⟨c.control.map (fun q => Flow.inner (flow P) q (block (P.code q)).start), bitStore c.store, c.output⟩

end MeanPayoff.ForestMachine

namespace MeanPayoff.ForestMachine
open BinaryData (Data)
open RegisterBits
open BinaryStack (applyOp)

def ValidOp {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data) : Prop :=
  match op with
  | .join i _ => 2 ≤ (s i).length
  | .move i _ _ _ | .copy i _ _ _ => s i ≠ []
  | _ => True

def afterBlock {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data) : Fin K → List Data :=
  match op with
  | .move i j _ _ => match s i with
      | [] => s
      | a :: xs => Function.update (Function.update s i xs) j (a :: s j)
  | .copy i j _ _ => match s i with
      | [] => s
      | a :: _ => Function.update s j (a :: s j)
  | _ => s

def blockBound {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data) : ℕ :=
  match op with
  | .move i _ _ _ => match s i with | [] => 1 | a :: _ => 6 * (BinaryData.encode a).length + 3
  | .copy i _ _ _ => match s i with | [] => 1 | a :: _ => 7 * (BinaryData.encode a).length + 3
  | _ => 1

theorem block_contract {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data)
    (h : ValidOp op s) (out : List Bool) (bits : ℕ → Bool) :
    advance (block op) bits ⟨some (block op).start, bitStore s, out⟩ (blockBound op s) =
      ⟨none, bitStore (afterBlock op s), out⟩ := by
  cases op with
  | move i j hij r =>
    cases hs : s i with
    | nil => simp [ValidOp, hs] at h
    | cons a xs =>
      dsimp only [block]
      have hm := move_tree i j hij (bitStore s) out a (encodeForest xs)
        (encodeForest (s j)) (by simp [hs]) (by simp) (by simp) (by simp) bits
      simpa only [blockBound, hs, afterBlock, bitStore_update, encodeForest_cons] using hm
  | copy i j hij r =>
    cases hs : s i with
    | nil => simp [ValidOp, hs] at h
    | cons a xs =>
      dsimp only [block]
      have hm := copy_tree i j hij (bitStore s) out a (encodeForest xs)
        (encodeForest (s j)) (by simp [hs]) (by simp) (by simp) (by simp) bits
      simpa only [blockBound, hs, afterBlock, bitStore_update, encodeForest_cons] using hm
  | nil i r | join i r | split i e n p | emit b r | coin z o | halt => rfl

theorem block_deterministic {K N : ℕ} (op : Instruction K N)
    (q : Fin (block op).states) (top : Option Bool) (b : Bool) :
    (block op).transition q top b = (block op).transition q top false := by
  cases op <;> rfl

theorem step_deterministic {K : ℕ} (P : RegisterBits.Program K)
    (h : ∀ q top b, P.transition q top b = P.transition q top false)
    (c : RegisterBits.Config P) (b : Bool) : RegisterBits.step P c b = RegisterBits.step P c false := by
  cases hc : c.control with
  | none => simp [RegisterBits.step, hc]
  | some q => simp only [RegisterBits.step, hc, h]

theorem advance_deterministic {K : ℕ} (P : RegisterBits.Program K)
    (h : ∀ q top b, P.transition q top b = P.transition q top false)
    (c : RegisterBits.Config P) (bits : ℕ → Bool) (n : ℕ) :
    advance P bits c n = advance P (fun _ => false) c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, ih, step_deterministic P h]

open scoped Classical

noncomputable def duration {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data) : ℕ :=
  if h : ∃ t, (advance (block op) (fun _ => false)
      ⟨some (block op).start, bitStore s, []⟩ t).control = none then Nat.find h else 0

theorem advance_output_irrelevant {K : ℕ} (P : RegisterBits.Program K)
    (c : RegisterBits.Config P) (out : List Bool) (bits : ℕ → Bool) (n : ℕ) :
    (advance P bits {c with output := out} n).control = (advance P bits c n).control ∧
    (advance P bits {c with output := out} n).stack = (advance P bits c n).stack := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [advance, RegisterBits.step]
    rw [ih.1]
    cases hc : (advance P bits c n).control with
    | none => exact ih
    | some q =>
      simp only [ih.2]
      cases ha : P.transition q ((advance P bits c n).stack (P.read q)).head? (bits n) <;>
        simp only [and_self]

theorem duration_spec {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data)
    (h : ValidOp op s) (out : List Bool) (bits : ℕ → Bool) :
    duration op s ≤ blockBound op s ∧
    (advance (block op) bits ⟨some (block op).start, bitStore s, out⟩ (duration op s)).control = none ∧
    (∀ j < duration op s,
      (advance (block op) bits ⟨some (block op).start, bitStore s, out⟩ j).control ≠ none) := by
  have hh := congrArg RegisterBits.Config.control (block_contract op s h [] (fun _ => false))
  have hex : ∃ t, (advance (block op) (fun _ => false)
      ⟨some (block op).start, bitStore s, []⟩ t).control = none := ⟨_, hh⟩
  simp only [duration, dite_eq_left hex]
  have he (j : ℕ) :
      (advance (block op) bits ⟨some (block op).start, bitStore s, out⟩ j).control =
      (advance (block op) (fun _ => false) ⟨some (block op).start, bitStore s, []⟩ j).control := by
    rw [advance_deterministic _ (block_deterministic op)]
    exact (advance_output_irrelevant (block op) ⟨some (block op).start, bitStore s, []⟩ out _ j).1
  refine ⟨Nat.find_min' hex hh, ?_, ?_⟩
  · rw [he]; exact Nat.find_spec hex
  · intro j hj; rw [he]; exact Nat.find_min hex hj

theorem macro_boundary {K : ℕ} (P : Program K) (q : Fin P.nodes) (s : Fin K → List Data)
    (h : ValidOp (P.code q) s) (out : List Bool) (bits : ℕ → Bool) :
    advance (compile P) bits (Flow.state (flow P) q (bitStore s) out) (duration (P.code q) s) =
      Flow.edge (flow P) q (bitStore (afterBlock (P.code q) s)) out := by
  obtain ⟨hb, hh, hn⟩ := duration_spec (P.code q) s h out bits
  have contract := block_contract (P.code q) s h out bits
  have he : advance (block (P.code q)) bits ⟨some (block (P.code q)).start, bitStore s, out⟩
      (duration (P.code q) s) = ⟨none, bitStore (afterBlock (P.code q) s), out⟩ := by
    rw [← contract]
    rw [show blockBound (P.code q) s = duration (P.code q) s +
      (blockBound (P.code q) s - duration (P.code q) s) by omega, BinaryData.Take.advance_add]
    symm
    exact advance_halted _ _ hh _ _
  change advance (Flow.compile (flow P)) bits
    (Flow.embed (flow P) q ⟨some (block (P.code q)).start, bitStore s, out⟩) _ = _
  have hh' := Flow.advance_inner (flow P) q
    (⟨some (block (P.code q)).start, bitStore s, out⟩) bits (duration (P.code q) s) hn
  exact hh'.trans (by rw [he]; rfl)
end MeanPayoff.ForestMachine
end

end OAI
