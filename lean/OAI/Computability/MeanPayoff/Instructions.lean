import OAI.Computability.MeanPayoff.Registers

namespace OAI

section

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance applyOp)

@[simp] theorem step_source {K : ℕ} (P : Program K) (q : Fin P.states)
    (bit : Bool) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.source q) xs ys out) bit =
      cfg P (.seek q bit ⟨(P.read q).val, by omega⟩) xs ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

theorem instruction {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (prefx : List (List Bool)) (hp : prefx.length = (P.read q).val)
    (xs tail out : List Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 2 * (encodeAll prefx).length + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
      advance (program P) bits
        (cfg P (.source q) (encodeAll prefx ++ encode xs ++ tail) [] out) n =
        sourceCfg P (localDest P q coin xs)
          (encodeAll prefx ++ encode (applyOp (localOp P q coin xs) xs) ++ tail) []
          (out ++ (localEmit P q coin xs).toList) := by
  obtain ⟨u, hu, hu4, hupdate⟩ := local_update P q coin xs tail (encodeAll prefx).reverse out
  let a := (encodeAll prefx).length
  refine ⟨(a + u + (a + 1)) + 1, by omega, by dsimp [a]; omega, ?_⟩
  intro bits hc
  rw [BinaryStack.advance_front, hc, step_source]
  have hfin : (⟨(P.read q).val, by omega⟩ : Fin (K + 1)) =
      ⟨prefx.length, by have := (P.read q).isLt; omega⟩ := by
    apply Fin.ext; exact hp.symm
  rw [hfin, List.append_assoc]
  rw [advance_add (a := a + u) (b := a + 1), advance_add (a := a) (b := u)]
  rw [seek_prefix P q coin prefx (by have := (P.read q).isLt; omega)]
  simp only [List.append_nil]
  rw [hupdate, show a + 1 = ((encodeAll prefx).reverse).length + 1 by simp [a], restore_all]
  simp [List.append_assoc]

end MeanPayoff.RegisterBits.Compile

namespace MeanPayoff.RegisterBits

@[ext] theorem Config.ext {K : ℕ} {P : Program K} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

def storeSize {K : ℕ} (s : Fin K → List Bool) : ℕ := ∑ i, (s i).length

def advance {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | n + 1 => step P (advance P bits c n) (bits n)

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]; rfl

namespace Compile

noncomputable def embed {K : ℕ} (P : Program K) (c : Config P) : BinaryStack.Config (program P) :=
  sourceCfg P c.control (encodeAll (List.ofFn c.stack)) [] c.output

theorem ofFn_split {K : ℕ} (s : Fin K → List Bool) (k : Fin K) :
    List.ofFn s = (List.ofFn s).take k.val ++ s k :: (List.ofFn s).drop (k.val + 1) := by
  have h : k.val < (List.ofFn s).length := by simp
  have ht := List.take_append_drop (k.val + 1) (List.ofFn s)
  rw [List.take_succ_eq_append_getElem h, List.getElem_ofFn] at ht
  simpa [List.append_assoc] using ht.symm

theorem ofFn_update {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    List.ofFn (Function.update s k xs) = (List.ofFn s).set k.val xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn, List.getElem_set]
  simp [Function.update_apply, Fin.ext_iff, eq_comm]

theorem encode_split {K : ℕ} (s : Fin K → List Bool) (k : Fin K) :
    encodeAll (List.ofFn s) = encodeAll ((List.ofFn s).take k.val) ++
      encode (s k) ++ encodeAll ((List.ofFn s).drop (k.val + 1)) := by
  conv_lhs => rw [ofFn_split s k]
  simp [encodeAll, List.append_assoc]

theorem encode_update {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    encodeAll (List.ofFn (Function.update s k xs)) = encodeAll ((List.ofFn s).take k.val) ++
      encode xs ++ encodeAll ((List.ofFn s).drop (k.val + 1)) := by
  rw [ofFn_update, List.set_eq_take_cons_drop xs (by simp)]
  simp [encodeAll, List.append_assoc]

@[simp] theorem encoded_size {K : ℕ} (s : Fin K → List Bool) :
    (encodeAll (List.ofFn s)).length = 2 * storeSize s + K := by
  simp [storeSize, List.map_ofFn, List.sum_ofFn]

theorem step_simulation {K : ℕ} (P : Program K) (c : Config P) (q : Fin P.states)
    (hq : c.control = some q) (coin : Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 * storeSize c.stack + 2 * K + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
        BinaryStack.advance (program P) bits (embed P c) n = embed P (RegisterBits.step P c coin) := by
  let k := P.read q
  let pref := (List.ofFn c.stack).take k.val
  have hp : pref.length = k.val := by simp [pref]
  obtain ⟨n, hn, hnb, hs⟩ := instruction P q coin pref hp (c.stack k)
    (encodeAll ((List.ofFn c.stack).drop (k.val + 1))) c.output
  have hpBound : (encodeAll pref).length ≤ 2 * storeSize c.stack + K := by
    have h := encode_split c.stack k
    have hl := congrArg List.length h
    simp only [encoded_size, List.length_append] at hl
    dsimp [pref]
    omega
  refine ⟨n, hn, by omega, ?_⟩
  intro bits hc
  have hin : embed P c = cfg P (.source q)
      (encodeAll pref ++ encode (c.stack k) ++ encodeAll ((List.ofFn c.stack).drop (k.val + 1))) [] c.output := by
    unfold embed
    rw [encode_split c.stack k, hq]
    rfl
  rw [hin, hs bits hc]
  cases he : P.transition q (c.stack k).head? coin with
  | none =>
    simp only [localDest, localOp, localEmit, he, Option.map_none, Option.getD_none, Option.bind_none,
      BinaryStack.applyOp, Option.toList_none, List.append_nil]
    change sourceCfg P none _ [] c.output = _
    rw [← encode_split c.stack k]
    have he' : P.transition q (c.stack (P.read q)).head? coin = none := he
    simp only [embed, RegisterBits.step, hq, he']
  | some a =>
    simp only [localDest, localOp, localEmit, he, Option.map_some, Option.getD_some, Option.bind_some]
    have he' : P.transition q (c.stack (P.read q)).head? coin = some a := he
    unfold embed
    simp only [RegisterBits.step, hq, he']
    rw [encode_update]

end Compile


 theorem update_size {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    storeSize (Function.update s k xs) + (s k).length = storeSize s + xs.length := by
  have he : (fun i => ((Function.update s k xs) i).length) =
      Function.update (fun i => (s i).length) k xs.length := by
    funext i
    by_cases h : i = k <;> simp [h]
  have h₁ := Finset.sum_update_of_mem (Finset.mem_univ k) (fun i => (s i).length) xs.length
  have h₂ := Finset.sum_update_of_mem (Finset.mem_univ k) (fun i => (s i).length) (s k).length
  simp only [Function.update_eq_self] at h₂
  unfold storeSize
  rw [he, h₁, h₂]
  omega

 theorem op_size (op : BinaryStack.Op) (xs : List Bool) :
    (BinaryStack.applyOp op xs).length ≤ xs.length + 1 := by
  cases op <;> cases xs <;> simp [BinaryStack.applyOp] ; omega

theorem step_size {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) :
    storeSize (step P c bit).stack ≤ storeSize c.stack + 1 := by
  unfold step
  cases hc : c.control with
  | none => simp
  | some q =>
    cases he : P.transition q (c.stack (P.read q)).head? bit with
    | none => simp [he]
    | some a =>
      simp only [he]
      have hs := update_size c.stack (P.read q) (BinaryStack.applyOp a.work (c.stack (P.read q)))
      have ho := op_size a.work (c.stack (P.read q))
      omega

 theorem advance_size {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) (n : ℕ) :
    storeSize (advance P bits c n).stack ≤ storeSize c.stack + n := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
    have h := step_size P (advance P bits c n) (bits n)
    simp only [advance]
    omega

namespace Compile

 theorem step_simulation_all {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 * storeSize c.stack + 2 * K + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
        BinaryStack.advance (program P) bits (embed P c) n = embed P (RegisterBits.step P c coin) := by
  cases hc : c.control with
  | none =>
    refine ⟨1, by omega, by omega, ?_⟩
    intro bits _
    have hh : (embed P c).control = none := by simp [embed, sourceCfg, hc] ; rfl
    rw [BinaryStack.advance_halted _ _ _ hh]
    simp [RegisterBits.step, hc]
  | some q => exact step_simulation P c q hc coin

noncomputable def clock {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) : ℕ :=
  (step_simulation_all P c coin).choose

theorem clock_pos {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) : 1 ≤ clock P c coin :=
  (step_simulation_all P c coin).choose_spec.1

theorem clock_bound {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) :
    clock P c coin ≤ 4 * storeSize c.stack + 2 * K + 6 :=
  (step_simulation_all P c coin).choose_spec.2.1

theorem clock_simulation {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (embed P c) (clock P c (bits 0)) =
      embed P (RegisterBits.step P c (bits 0)) :=
  (step_simulation_all P c (bits 0)).choose_spec.2.2 bits rfl

end Compile


def initial {K : ℕ} (P : Program K) (input : List Bool) : Config P :=
  ⟨some P.start, fun i => if i.val = 0 then input else [], []⟩

namespace Compile
open BinaryStack (advance applyOp)

def escape : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escape bs

@[simp] theorem escape_append (a b : List Bool) : escape (a ++ b) = escape a ++ escape b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escape, ih]

theorem encode_escape (xs : List Bool) : encode xs = escape xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, escape, ih]

@[simp] theorem encodeAll_replicate_nil (n : ℕ) :
    encodeAll (List.replicate n []) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, encodeAll, encode, ih]

theorem encode_initial {K : ℕ} (P : Program K) (input : List Bool) :
    encodeAll (List.ofFn (RegisterBits.initial P input).stack) =
      escape input ++ List.replicate K false := by
  cases K with
  | zero => exact Fin.elim0 (P.read P.start)
  | succ K =>
    have he : (fun j : Fin K => (RegisterBits.initial P input).stack j.succ) = fun _ => [] := by
      funext j; simp [RegisterBits.initial]
    rw [List.ofFn_succ, he]
    simp [RegisterBits.initial, encodeAll, encode_escape, List.replicate_succ,
      List.append_assoc, List.ofFn_const]

@[simp] theorem init_move_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (b bit : Bool) :
    BinaryStack.step (program P) (cfg P .initMove (b :: xs) ys out) bit =
      cfg P .initMove xs (b :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

theorem init_move_all {K : ℕ} (P : Program K) (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P .initMove xs ys out) xs.length =
      cfg P .initMove [] (xs.reverse ++ ys) out := by
  induction xs generalizing ys bits with
  | nil => simp [BinaryStack.advance]
  | cons b xs ih =>
    rw [List.length_cons, BinaryStack.advance_front, init_move_step, ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem init_move_empty {K : ℕ} (P : Program K) (ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initMove [] ys out) bit =
      cfg P (.initPad ⟨K, by omega⟩) [] ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_pad_zero {K : ℕ} (P : Program K) (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P (.initPad 0) xs ys out) bit =
      cfg P .initRestore xs ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_pad_succ {K : ℕ} (P : Program K) (n : ℕ) (hn : n + 1 < K + 1)
    (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P (.initPad ⟨n + 1, hn⟩) xs ys out) bit =
      cfg P (.initPad ⟨n, by omega⟩) (false :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

theorem init_pad_all {K : ℕ} (P : Program K) (n : ℕ) (hn : n < K + 1)
    (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P (.initPad ⟨n, hn⟩) xs ys out) (n + 1) =
      cfg P .initRestore (List.replicate n false ++ xs) ys out := by
  induction n generalizing xs bits with
  | zero => simp [BinaryStack.advance]
  | succ n ih =>
    rw [BinaryStack.advance_front, init_pad_succ, ih]
    rw [List.replicate_succ', List.append_assoc]
    rfl

@[simp] theorem init_restore_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (b bit : Bool) :
    BinaryStack.step (program P) (cfg P .initRestore xs (b :: ys) out) bit =
      cfg P .initTag (b :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_tag_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initTag xs ys out) bit =
      cfg P .initRestore (true :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_restore_empty {K : ℕ} (P : Program K) (xs out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initRestore xs [] out) bit =
      cfg P (.source P.start) xs [] out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

theorem init_restore_all {K : ℕ} (P : Program K) (xs ys out : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (cfg P .initRestore xs ys out) (2 * ys.length + 1) =
      cfg P (.source P.start) (escape ys.reverse ++ xs) [] out := by
  induction ys generalizing xs bits with
  | nil => simp [BinaryStack.advance, escape]
  | cons b ys ih =>
    rw [List.length_cons, show 2 * (ys.length + 1) + 1 = (2 * ys.length + 1 + 1) + 1 by omega,
      BinaryStack.advance_front, init_restore_step, BinaryStack.advance_front, init_tag_step, ih]
    simp [List.reverse_cons, escape, List.append_assoc]

theorem initial_cfg {K : ℕ} (P : Program K) (input : List Bool) :
    BinaryStack.initial (program P) input = cfg P .initMove input [] [] := by
  apply BinaryStack.Config.ext
  · rfl
  · funext i; fin_cases i <;> simp [BinaryStack.initial, cfg]
  · rfl

theorem initialize_correct {K : ℕ} (P : Program K) (input : List Bool) (bits : ℕ → Bool) :
    BinaryStack.advance (program P) bits (BinaryStack.initial (program P) input)
        (3 * input.length + K + 3) = embed P (RegisterBits.initial P input) := by
  rw [initial_cfg]
  have hn : 3 * input.length + K + 3 = (input.length + 1) + (K + 1) + (2 * input.length + 1) := by omega
  rw [hn, advance_add (a := input.length + 1 + (K + 1)) (b := 2 * input.length + 1),
    advance_add (a := input.length + 1) (b := K + 1)]
  have hm : BinaryStack.advance (program P) bits (cfg P .initMove input [] []) (input.length + 1) =
      cfg P (.initPad ⟨K, by omega⟩) [] input.reverse [] := by
    change BinaryStack.step (program P)
      (BinaryStack.advance (program P) bits (cfg P .initMove input [] []) input.length) (bits input.length) = _
    rw [init_move_all, List.append_nil, init_move_empty]
  rw [hm, init_pad_all, List.append_nil]
  rw [show 2 * input.length + 1 = 2 * input.reverse.length + 1 by simp, init_restore_all]
  simp only [List.reverse_reverse]
  unfold embed
  rw [encode_initial]
  rfl

end Compile
end MeanPayoff.RegisterBits
end

end OAI
