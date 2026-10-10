import OAI.Computability.MeanPayoff.Instructions

namespace OAI

section
namespace MeanPayoff.BinaryStack
@[simp] theorem advance_initial (P : Program) (code : List Bool) (bits : ℕ → Bool) (n : ℕ) :
    advance P bits (initial P code) n = run P code bits n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, run, ih]
end MeanPayoff.BinaryStack

namespace MeanPayoff.RandomTree

def wait {α : Type} : ℕ → RandomTree α → RandomTree α
  | 0, t => t
  | n + 1, t => .coin (wait n t) (wait n t)

@[simp] theorem expect_wait {α : Type} (n : ℕ) (t : RandomTree α) (f : α → ℚ) :
    (wait n t).expect f = t.expect f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wait, expect, ih]; ring

@[simp] theorem depth_wait {α : Type} (n : ℕ) (t : RandomTree α) :
    (wait n t).bitDepth = n + t.bitDepth := by
  induction n with
  | zero => simp [wait]
  | succ n ih => simp [wait, bitDepth, ih]; omega

@[simp] theorem all_wait {α : Type} (n : ℕ) (t : RandomTree α) (Q : α → Prop) :
    (wait n t).All Q ↔ t.All Q := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wait, All, ih]

@[simp] theorem consume_wait {α : Type} (n : ℕ) (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    (wait n t).consume bits pos = t.consume bits (pos + n) := by
  induction n generalizing pos with
  | zero => simp [wait]
  | succ n ih => simp only [wait, consume, ih]; split <;> congr 1 <;> omega

end MeanPayoff.RandomTree
namespace MeanPayoff.RegisterBits
open RandomTree

def tree {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n + 1, c => .coin (tree P n (step P c false)) (tree P n (step P c true))

namespace Compile

noncomputable def schedule {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n + 1, c => .coin
      (wait (clock P c false - 1) (schedule P n (step P c false)))
      (wait (clock P c true - 1) (schedule P n (step P c true)))

theorem schedule_expect {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (f : Config P → ℚ) :
    (schedule P n c).expect f = (tree P n c).expect f := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, expect, expect_wait, ih]

theorem schedule_all {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (Q : Config P → Prop) :
    (schedule P n c).All Q ↔ (tree P n c).All Q := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, All, all_wait, ih]

def overhead (K S n : ℕ) : ℕ := n * (4 * (S + n) + 2 * K + 6)

theorem schedule_depth {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) :
    (schedule P n c).bitDepth ≤ overhead K (storeSize c.stack) n := by
  induction n generalizing c with
  | zero => simp [schedule, bitDepth, overhead]
  | succ n ih =>
    have hbranch (b : Bool) :
        clock P c b - 1 + (schedule P n (step P c b)).bitDepth + 1 ≤
          overhead K (storeSize c.stack) (n + 1) := by
      have hs := step_size P c b
      have hi := ih (step P c b)
      have ht := clock_bound P c b
      have hp := clock_pos P c b
      have hm := Nat.mul_le_mul_left (4 * n) hs
      have he : clock P c b - 1 + 1 = clock P c b := by omega
      unfold overhead at *
      nlinarith only [hi, ht, he, hm]
    simp only [schedule, bitDepth, depth_wait]
    have h₀ := hbranch false
    have h₁ := hbranch true
    omega

theorem consume_schedule_step {K : ℕ} (P : Program K) (n : ℕ) (c : Config P)
    (bits : ℕ → Bool) (pos : ℕ) :
    (schedule P (n + 1) c).consume bits pos =
      (schedule P n (step P c (bits pos))).consume bits (pos + clock P c (bits pos)) := by
  have ht := clock_pos P c (bits pos)
  simp only [schedule, consume, consume_wait]
  cases hb : bits pos <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at * <;>
    congr 1 <;> omega

theorem consume_simulation {K : ℕ} (P : Program K) (n : ℕ) (c : Config P)
    (bits : ℕ → Bool) (pos : ℕ) :
    let r := (schedule P n c).consume bits pos
    BinaryStack.advance (program P) (fun j => bits (pos + j)) (embed P c) (r.2 - pos) = embed P r.1 := by
  induction n generalizing c pos with
  | zero => simp [schedule, consume, BinaryStack.advance]
  | succ n ih =>
    simp only [consume_schedule_step]
    let a := clock P c (bits pos)
    let d := step P c (bits pos)
    let r := (schedule P n d).consume bits (pos + a)
    have hr : pos + a ≤ r.2 := (consume_path (schedule P n d) bits (pos + a)).1
    have hi := ih d (pos + a)
    change BinaryStack.advance (program P) (fun j => bits (pos + j)) (embed P c) (r.2 - pos) = _
    rw [show r.2 - pos = a + (r.2 - (pos + a)) by omega, advance_add]
    have hc := clock_simulation P c (fun j => bits (pos + j))
    simp only [Nat.add_zero] at hc
    rw [hc]
    simpa only [Nat.add_assoc] using hi

noncomputable def initializedTree {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) :
    RandomTree (Config P) :=
  wait (3 * input.length + K + 3) (schedule P n (initial P input))

theorem initialized_depth {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) :
    (initializedTree P input n).bitDepth ≤
      3 * input.length + K + 3 + overhead K (storeSize (initial P input).stack) n := by
  rw [initializedTree, depth_wait]
  exact Nat.add_le_add_left (schedule_depth P n _) _

theorem initialized_simulation {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (bits : ℕ → Bool) :
    let r := (initializedTree P input n).consume bits 0
    BinaryStack.run (program P) input bits r.2 = embed P r.1 := by
  simp only [initializedTree, consume_wait, Nat.zero_add]
  let a := 3 * input.length + K + 3
  let r := (schedule P n (initial P input)).consume bits a
  have hr : a ≤ r.2 := (consume_path (schedule P n (initial P input)) bits a).1
  rw [← BinaryStack.advance_initial]
  change BinaryStack.advance (program P) bits (BinaryStack.initial (program P) input) r.2 = _
  rw [show r.2 = a + (r.2 - a) by omega, advance_add, initialize_correct]
  exact consume_simulation P n (initial P input) bits a

end Compile
end MeanPayoff.RegisterBits

namespace MeanPayoff.BinaryStack

theorem run_after_halt (P : Program) (input : List Bool) (bits : ℕ → Bool) (a b : ℕ)
    (ha : (run P input bits a).control = none) (hab : a ≤ b) :
    run P input bits b = run P input bits a := by
  rw [← advance_initial, show b = a + (b - a) by omega,
    RegisterBits.Compile.advance_add, advance_initial, advance_halted P _ _ ha]

end MeanPayoff.BinaryStack
namespace MeanPayoff.RegisterBits.Compile
open RandomTree

theorem embed_halted {K : ℕ} (P : Program K) (c : Config P) (hc : c.control = none) :
    (embed P c).control = none := by simp [embed, sourceCfg, hc]; rfl

theorem initialized_all {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) (Q : Config P → Prop) :
    (initializedTree P input n).All Q ↔ (tree P n (initial P input)).All Q := by
  simp only [initializedTree, all_wait, schedule_all]

theorem initialized_expect {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) (f : Config P → ℚ) :
    (initializedTree P input n).expect f = (tree P n (initial P input)).expect f := by
  simp only [initializedTree, expect_wait, schedule_expect]

def bound {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) : ℕ :=
  3 * input.length + K + 3 + overhead K (storeSize (initial P input).stack) n

theorem padded_run {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (bits : ℕ → Bool) :
    BinaryStack.run (program P) input bits (bound P input n) =
      embed P ((initializedTree P input n).read bits) := by
  let t := initializedTree P input n
  let r := t.consume bits 0
  have hp : Path t r.1 r.2 := by simpa only [Nat.sub_zero] using (consume_path t bits 0).2
  have hr : r.2 ≤ bound P input n := hp.depth_le.trans (initialized_depth P input n)
  have ha : r.1.control = none := hp.all ((initialized_all P input n _).2 hh)
  have hs : BinaryStack.run (program P) input bits r.2 = embed P r.1 := initialized_simulation P input n bits
  have halted : (BinaryStack.run (program P) input bits r.2).control = none := by
    rw [hs]; exact embed_halted P r.1 ha
  rw [BinaryStack.run_after_halt _ _ _ r.2 _ halted hr, hs]
  have he : r.1 = t.read bits := by simpa only [Nat.zero_add] using consume_read t bits 0
  rw [he]

noncomputable def machine {K : ℕ} (P : Program K) : MeanPayoff.Machine :=
  BinaryStack.machine (program P)

theorem machine_packet {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (bits : Fin (2 * bound P input n) → Bool) :
    let out := ((initializedTree P input n).readPrefix (TwoPhase.even bits)).output
    let c := MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)
    c.control = none ∧ c.tape 2 = BinaryStack.cells out 0 := by
  obtain ⟨h, he⟩ := BinaryStack.simulate (program P) input (padBits bits) (bound P input n)
  dsimp only [machine]
  rw [he, TwoPhase.pad_even, padded_run P input n hh]
  let c := (initializedTree P input n).read (padBits (TwoPhase.even bits))
  have hc : c.control = none := by
    have hp := (consume_path (initializedTree P input n) (padBits (TwoPhase.even bits)) 0).2
    have ha := hp.all ((initialized_all P input n _).2 hh)
    simpa only [consume_read, Nat.zero_add] using ha
  constructor
  · exact (BinaryStack.concrete_halted _ _ _).2 (embed_halted P c hc)
  · rfl

open scoped Classical

theorem machine_probability {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ)
    (hh : (tree P n (initial P input)).All (fun c => c.control = none))
    (Q : List Bool → Prop) :
    ((Finset.univ.filter (fun bits : Fin (2 * bound P input n) → Bool =>
      ∃ out, Q out ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)).control = none ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * bound P input n)).tape 2 =
          BinaryStack.cells out 0)).card : ℚ) ≥
      (2 : ℚ) ^ (2 * bound P input n) *
        (tree P n (initial P input)).probability (fun c => Q c.output) := by
  let T := bound P input n
  let t := initializedTree P input n
  have ht : t.bitDepth ≤ T := initialized_depth P input n
  have hprob : t.probability (fun c => Q c.output) =
      (tree P n (initial P input)).probability (fun c => Q c.output) :=
    initialized_expect P input n _
  have hc := prefix_probability t (fun c => Q c.output) T ht
  rw [hprob] at hc
  have he := TwoPhase.successful_count T (fun bits => Q (t.readPrefix bits).output)
  have hsub : (Finset.univ.filter (fun bits : Fin (2 * T) → Bool =>
      Q (t.readPrefix (TwoPhase.even bits)).output)).card ≤
      (Finset.univ.filter (fun bits : Fin (2 * T) → Bool =>
      ∃ out, Q out ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * T)).control = none ∧
        (MeanPayoff.run (machine P) input (padBits bits) (2 * T)).tape 2 =
          BinaryStack.cells out 0)).card := by
    apply Finset.card_le_card
    intro bits hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨_, hb, machine_packet P input n hh bits⟩
  rw [he] at hsub
  have hcast : ((2 ^ T * (Finset.univ.filter (fun bits : Fin T → Bool => Q (t.readPrefix bits).output)).card : ℕ) : ℚ) ≤ _ :=
    (Nat.cast_le (α := ℚ)).2 hsub
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [hc] at hcast
  convert hcast using 1
  rw [show 2 * T = T + T by omega, pow_add]; ring

end MeanPayoff.RegisterBits.Compile
namespace MeanPayoff
namespace BinaryData

inductive Data where
  | nil
  | pair (left right : Data)
  deriving DecidableEq

def encode : Data → List Bool
  | .nil => [false]
  | .pair a b => true :: encode a ++ encode b

@[simp] theorem encode_nonempty (a : Data) : encode a ≠ [] := by cases a <;> simp [encode]
@[simp] theorem encode_positive (a : Data) : 0 < (encode a).length := List.length_pos_iff.mpr (encode_nonempty a)

namespace Take
open RegisterBits
open BinaryStack (Op applyOp)

inductive Label where
  | start | check | read | put (b : Bool) | depth (b : Bool)
  | restore | restorePut (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem dec (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 4 where
  states := Fintype.card Label
  start := enc .start
  read q := match equiv.symm q with
    | .start | .check | .depth _ => 3
    | .read => 0
    | .put _ | .restore => 2
    | .restorePut _ => 1
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc .check, .push true, none⟩
    | .check => some ⟨enc (if top.isSome then .read else .restore), .keep, none⟩
    | .read => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc (.depth b), .push b, none⟩
    | .depth b => some ⟨enc .check, if b then .push true else .pop, none⟩
    | .restore => top.map fun b => ⟨enc (.restorePut b), .pop, none⟩
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
    RegisterBits.step program (cfg .restore xs ys (b :: zs) ds out) bit = cfg (.restorePut b) xs ys zs ds out := by
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
    advance program bits (cfg .restore xs ys zs ds out) (2 * zs.length + 1) =
      stopped xs (zs.reverse ++ ys) [] ds out := by
  induction zs generalizing ys bits with
  | nil => simp [advance, restore_empty]
  | cons b zs ih =>
    rw [List.length_cons, show 2 * (zs.length + 1) + 1 = (2 * zs.length + 1 + 1) + 1 by omega,
      advance_front, restore_step, advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem takes (t : Data) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .start (encode t ++ xs) ys [] [] out)
      (6 * (encode t).length + 3) = stopped xs (encode t ++ ys) [] [] out := by
  rw [show 6 * (encode t).length + 3 = (4 * (encode t).length + 1 + (2 * (encode t).length + 1)) + 1 by omega,
    advance_front, start_step, advance_add (a := 4 * (encode t).length + 1)]
  have hs (bits : ℕ → Bool) : advance program bits (cfg .check (encode t ++ xs) ys [] [true] out)
      (4 * (encode t).length + 1) = cfg .restore xs ys (encode t).reverse [] out := by
    rw [advance, scan, List.append_nil, check_empty]
  rw [hs]
  simpa using restore_all xs ys (encode t).reverse [] out (fun j => bits (4 * (encode t).length + 1 + j + 1))

end Take
end BinaryData
end MeanPayoff
end

end OAI
