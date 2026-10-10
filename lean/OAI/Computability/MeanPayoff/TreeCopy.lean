import OAI.Computability.MeanPayoff.FiniteTrees

namespace OAI

section
namespace MeanPayoff.RegisterBits
open BinaryStack (applyOp)

def rename {K N : ℕ} (P : Program K) (f : Fin K → Fin N) : Program N where
  states := P.states
  start := P.start
  read q := f (P.read q)
  transition := P.transition

noncomputable def install {K N : ℕ} (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) : Fin N → List Bool :=
  fun j => if h : ∃ i, f i = j then s (Classical.choose h) else ambient j

@[simp] theorem install_at {K N : ℕ} (f : Fin K → Fin N) (hf : Function.Injective f)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (i : Fin K) :
    install f ambient s (f i) = s i := by
  unfold install
  split_ifs with h
  · rw [hf (Classical.choose_spec h)]
  · exact False.elim (h ⟨i, rfl⟩)

@[simp] theorem install_off {K N : ℕ} (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (j : Fin N)
    (hj : ∀ i, f i ≠ j) : install f ambient s j = ambient j := by
  simp [install, not_exists.mpr hj]

theorem install_update {K N : ℕ} (f : Fin K → Fin N) (hf : Function.Injective f)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (i : Fin K) (xs : List Bool) :
    install f ambient (Function.update s i xs) = Function.update (install f ambient s) (f i) xs := by
  funext j
  by_cases h : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := h
    simp only [install_at f hf]
    by_cases hi : k = i
    · subst k; simp
    · have hfi : f k ≠ f i := fun he => hi (hf he)
      simp [Function.update_of_ne hi, Function.update_of_ne hfi, install_at f hf]
  · have hi : j ≠ f i := by rintro rfl; exact h ⟨i, rfl⟩
    simp only [Function.update_of_ne hi]
    simp [install, h]

noncomputable def renamed {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (c : Config P) : Config (rename P f) :=
  ⟨c.control, install f ambient c.stack, c.output⟩

theorem rename_step {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (hf : Function.Injective f) (ambient : Fin N → List Bool) (c : Config P) (bit : Bool) :
    RegisterBits.step (rename P f) (renamed P f ambient c) bit =
      renamed P f ambient (RegisterBits.step P c bit) := by
  cases hc : c.control with
  | none => simp [RegisterBits.step, renamed, hc]
  | some q =>
    simp only [RegisterBits.step, renamed, hc, rename, install_at f hf]
    cases ha : P.transition q (c.stack (P.read q)).head? bit with
    | none => rfl
    | some a => simp only [install_update f hf]

theorem rename_advance {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (hf : Function.Injective f) (ambient : Fin N → List Bool) (c : Config P)
    (bits : ℕ → Bool) (n : ℕ) :
    advance (rename P f) bits (renamed P f ambient c) n =
      renamed P f ambient (advance P bits c n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, ih, rename_step P f hf]

@[simp] theorem halted_step {K : ℕ} (P : Program K) (c : Config P) (h : c.control = none)
    (bit : Bool) : RegisterBits.step P c bit = c := by simp [RegisterBits.step, h]

theorem advance_halted {K : ℕ} (P : Program K) (c : Config P) (h : c.control = none)
    (bits : ℕ → Bool) (n : ℕ) : advance P bits c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, ih, halted_step P c h]

theorem first_termination {K : ℕ} (P : Program K) (c : Config P)
    (bits : ℕ → Bool) (N : ℕ) (h : (advance P bits c N).control = none) :
    ∃ t ≤ N, (advance P bits c t).control = none ∧
      (∀ j < t, (advance P bits c j).control ≠ none) ∧
      advance P bits c t = advance P bits c N := by
  have hex : ∃ j, (advance P bits c j).control = none := ⟨N, h⟩
  let t := Nat.find hex
  have ht : (advance P bits c t).control = none := Nat.find_spec hex
  have hb : t ≤ N := Nat.find_min' hex h
  refine ⟨t, hb, ht, ?_, ?_⟩
  · intro j hj; exact Nat.find_min hex hj
  · rw [show N = t + (N - t) by omega, BinaryData.Take.advance_add, advance_halted P _ ht]

namespace Flow

structure Program (K : ℕ) where
  nodes : ℕ
  start : Fin nodes
  block : Fin nodes → RegisterBits.Program K
  read : Fin nodes → Fin K
  next : Fin nodes → Option Bool → Bool → Option (Act nodes)

abbrev Labels {K : ℕ} (P : Program K) :=
  (Σ q : Fin P.nodes, Fin (P.block q).states) ⊕ Fin P.nodes
noncomputable def equiv {K : ℕ} (P : Program K) : Labels P ≃ Fin (Fintype.card (Labels P)) :=
  Fintype.equivFin _
noncomputable def inner {K : ℕ} (P : Program K) (q : Fin P.nodes) (p : Fin (P.block q).states) :=
  equiv P (.inl ⟨q, p⟩)
noncomputable def boundary {K : ℕ} (P : Program K) (q : Fin P.nodes) := equiv P (.inr q)
@[simp] theorem dec_inner {K : ℕ} (P : Program K) (q : Fin P.nodes) (p : Fin (P.block q).states) :
    (equiv P).symm (inner P q p) = .inl ⟨q, p⟩ := (equiv P).symm_apply_apply _
@[simp] theorem dec_boundary {K : ℕ} (P : Program K) (q : Fin P.nodes) :
    (equiv P).symm (boundary P q) = .inr q := (equiv P).symm_apply_apply _

noncomputable def compile {K : ℕ} (P : Program K) : RegisterBits.Program K where
  states := Fintype.card (Labels P)
  start := inner P P.start (P.block P.start).start
  read q := match (equiv P).symm q with
    | .inl ⟨p, q⟩ => (P.block p).read q
    | .inr p => P.read p
  transition q top bit := match (equiv P).symm q with
    | .inl ⟨p, q⟩ => some (match (P.block p).transition q top bit with
        | none => ⟨boundary P p, .keep, none⟩
        | some a => ⟨inner P p a.next, a.work, a.emit⟩)
    | .inr p => (P.next p top bit).map fun a =>
        ⟨inner P a.next (P.block a.next).start, a.work, a.emit⟩

noncomputable def embed {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p)) :
    Config (compile P) :=
  ⟨some (c.control.elim (boundary P p) (inner P p)), c.stack, c.output⟩

noncomputable def state {K : ℕ} (P : Program K) (p : Fin P.nodes)
    (s : Fin K → List Bool) (out : List Bool) : Config (compile P) :=
  ⟨some (inner P p (P.block p).start), s, out⟩

noncomputable def edge {K : ℕ} (P : Program K) (p : Fin P.nodes)
    (s : Fin K → List Bool) (out : List Bool) : Config (compile P) :=
  ⟨some (boundary P p), s, out⟩

theorem step_inner {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p))
    (hc : c.control ≠ none) (bit : Bool) :
    RegisterBits.step (compile P) (embed P p c) bit =
      embed P p (RegisterBits.step (P.block p) c bit) := by
  cases he : c.control with
  | none => exact False.elim (hc he)
  | some q =>
    simp only [RegisterBits.step, embed, he, Option.elim_some, compile, dec_inner]
    cases ha : (P.block p).transition q (c.stack ((P.block p).read q)).head? bit with
    | none =>
      apply BinaryData.Take.config_ext
      · rfl
      · funext k; simp [applyOp]
      · simp
    | some a => rfl

theorem advance_inner {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p))
    (bits : ℕ → Bool) (n : ℕ)
    (hc : ∀ j < n, (advance (P.block p) bits c j).control ≠ none) :
    advance (compile P) bits (embed P p c) n = embed P p (advance (P.block p) bits c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RegisterBits.step (compile P) (advance (compile P) bits (embed P p c) n) (bits n) = _
    rw [ih (fun j hj => hc j (by omega)), step_inner P p _ (hc n (by omega))]
    rfl

theorem macro_runs {K : ℕ} (P : Program K) (p : Fin P.nodes) (s : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (h : (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).control = none) :
    ∃ t ≤ N, advance (compile P) bits (state P p s out) t =
      edge P p (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).stack
        (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).output := by
  obtain ⟨t, ht, hh, hn, he⟩ := first_termination (P.block p) ⟨some _, s, out⟩ bits N h
  refine ⟨t, ht, ?_⟩
  change advance (compile P) bits (embed P p ⟨some _, s, out⟩) t = _
  rw [advance_inner P p _ bits t hn, he]
  simp only [embed, h, edge]
  rfl

theorem step_boundary {K : ℕ} (P : Program K) (p : Fin P.nodes) (s : Fin K → List Bool)
    (out : List Bool) (bit : Bool) :
    RegisterBits.step (compile P) (edge P p s out) bit =
      match P.next p (s (P.read p)).head? bit with
      | none => ⟨none, s, out⟩
      | some a => state P a.next (Function.update s (P.read p) (applyOp a.work (s (P.read p))))
          (out ++ a.emit.toList) := by
  simp only [RegisterBits.step, edge, compile, dec_boundary]
  cases P.next p (s (P.read p)).head? bit <;> rfl

end Flow
end MeanPayoff.RegisterBits
namespace MeanPayoff
namespace BinaryData
namespace Copy
open RegisterBits
open BinaryStack (Op applyOp)

inductive Label where
  | start | check | read | put (b : Bool) | depth (b : Bool)
  | restore | restoreSource (b : Bool) | restorePut (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem dec (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 4 where
  states := Fintype.card Label
  start := enc .start
  read q := match equiv.symm q with
    | .start | .check | .depth _ => 3
    | .read | .restoreSource _ => 0
    | .put _ | .restore => 2
    | .restorePut _ => 1
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc .check, .push true, none⟩
    | .check => some ⟨enc (if top.isSome then .read else .restore), .keep, none⟩
    | .read => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc (.depth b), .push b, none⟩
    | .depth b => some ⟨enc .check, if b then .push true else .pop, none⟩
    | .restore => top.map fun b => ⟨enc (.restoreSource b), .pop, none⟩
    | .restoreSource b => some ⟨enc (.restorePut b), .push b, none⟩
    | .restorePut b => some ⟨enc .restore, .push b, none⟩

noncomputable def cfg (q : Label) (xs ys zs ds out : List Bool) : Config program :=
  ⟨some (enc q), ![xs, ys, zs, ds], out⟩
noncomputable def stopped (xs ys zs ds out : List Bool) : Config program :=
  ⟨none, ![xs, ys, zs, ds], out⟩

@[ext] theorem config_ext {K : ℕ} {P : Program K} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (RegisterBits.step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RegisterBits.step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]
    rfl

theorem advance_add {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (a b : ℕ) :
    advance P bits c (a + b) = advance P (fun j => bits (a + j)) (advance P bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change RegisterBits.step P (advance P bits c (a + b)) (bits (a + b)) = _
    rw [ih]
    rfl

@[simp] theorem start_step (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .start xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem check_step (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs (a :: ds) out) bit = cfg .read xs ys zs (a :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem read_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .read (b :: xs) ys zs ds out) bit = cfg (.put b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem put_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.put b) xs ys zs ds out) bit = cfg (.depth b) xs ys (b :: zs) ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_false (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg (.depth false) xs ys zs (a :: ds) out) bit = cfg .check xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_true (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg (.depth true) xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

theorem scan_nil (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (false :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (false :: zs) ds out := by
  simp [advance, check_step, read_step, put_step, depth_false]

theorem scan_pair (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (true :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (true :: zs) (true :: true :: ds) out := by
  simp [advance, check_step, read_step, put_step, depth_true]

theorem scan (t : Data) (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (encode t ++ xs) ys zs (true :: ds) out)
      (4 * (encode t).length) = cfg .check xs ys ((encode t).reverse ++ zs) ds out := by
  induction t generalizing xs zs ds bits with
  | nil => simpa [encode] using scan_nil xs ys zs ds out bits
  | pair a b ia ib =>
    simp only [encode, List.length_cons, List.length_append, List.cons_append]
    have hn : 4 * (1 + (encode a).length + (encode b).length) =
        4 + 4 * (encode a).length + 4 * (encode b).length := by omega
    rw [show 4 * ((encode a).length + (encode b).length + 1) =
      4 + 4 * (encode a).length + 4 * (encode b).length by omega,
      advance_add (a := 4 + 4 * (encode a).length) (b := 4 * (encode b).length),
      advance_add (a := 4), scan_pair, List.append_assoc, ia, ib]
    simp [List.reverse_cons, List.reverse_append, List.append_assoc]

@[simp] theorem check_empty (xs ys zs out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs [] out) bit = cfg .restore xs ys zs [] out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys (b :: zs) ds out) bit = cfg (.restoreSource b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_source (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.restoreSource b) xs ys zs ds out) bit =
      cfg (.restorePut b) (b :: xs) ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_put (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.restorePut b) xs ys zs ds out) bit = cfg .restore xs (b :: ys) zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_empty (xs ys ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys [] ds out) bit = stopped xs ys [] ds out := by
  simp [RegisterBits.step, program, cfg, stopped]

theorem restore_all (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .restore xs ys zs ds out) (3 * zs.length + 1) =
      stopped (zs.reverse ++ xs) (zs.reverse ++ ys) [] ds out := by
  induction zs generalizing xs ys bits with
  | nil => simp [advance, restore_empty]
  | cons b zs ih =>
    rw [List.length_cons, show 3 * (zs.length + 1) + 1 = ((3 * zs.length + 1 + 1) + 1) + 1 by omega,
      advance_front, restore_step, advance_front, restore_source, advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem copies (t : Data) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .start (encode t ++ xs) ys [] [] out)
      (7 * (encode t).length + 3) = stopped (encode t ++ xs) (encode t ++ ys) [] [] out := by
  rw [show 7 * (encode t).length + 3 = (4 * (encode t).length + 1 + (3 * (encode t).length + 1)) + 1 by omega,
    advance_front, start_step, advance_add (a := 4 * (encode t).length + 1)]
  have hs (bits : ℕ → Bool) : advance program bits (cfg .check (encode t ++ xs) ys [] [true] out)
      (4 * (encode t).length + 1) = cfg .restore xs ys (encode t).reverse [] out := by
    rw [advance, scan, List.append_nil, check_empty]
  rw [hs]
  simpa using restore_all xs ys (encode t).reverse [] out (fun j => bits (4 * (encode t).length + 1 + j + 1))

end Copy
end BinaryData
end MeanPayoff
end

end OAI
