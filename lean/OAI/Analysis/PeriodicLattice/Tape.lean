import OAI.Analysis.PeriodicLattice.PlanarFlow

namespace OAI

/-! Tape digits, stack evolution and effective local transition tables. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingTape {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace MachineFacts

theorem lookup_bounds {M : Machine} (hM : M.WellFormed) {q a : ℕ} {I : Instruction}
    (hI : M.lookup q a = some I) : I.nextState < M.states ∧ I.writeSymbol < M.symbols := by
  have hq : q < M.table.length := by
    by_contra h
    simp only [Machine.lookup, List.getD_eq_default _ _ (Nat.le_of_not_gt h),
      List.getD_nil] at hI
    contradiction
  have ha : a < (M.table[q]).length := by
    by_contra h
    simp only [Machine.lookup, List.getD_eq_getElem _ _ hq,
      List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at hI
    contradiction
  apply hM.2.2.2.2.2 (M.table[q]) (List.getElem_mem hq)
    ((M.table[q])[a]) (List.getElem_mem ha) I
  simpa only [Machine.lookup, List.getD_eq_getElem _ _ hq,
    List.getD_eq_getElem _ _ ha] using hI

end MachineFacts

namespace TapeDigits

def digit (b N i : ℕ) : ℕ := N / b ^ i % b

@[simp] theorem digit_zero (b N : ℕ) : digit b N 0 = N % b := by simp [digit]

@[simp] theorem digit_blank (b i : ℕ) : digit b 0 i = 0 := by simp [digit]

theorem digit_succ (b N i : ℕ) : digit b N (i + 1) = digit b (N / b) i := by
  simp only [digit, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

@[simp] theorem digit_cons_zero {b a : ℕ} (ha : a < b) (N : ℕ) :
    digit b (a + b * N) 0 = a := by simp [Nat.mod_eq_of_lt ha]

@[simp] theorem digit_cons_succ {b a : ℕ} (ha : a < b) (N i : ℕ) :
    digit b (a + b * N) (i + 1) = digit b N i := by
  rw [digit_succ]
  simp only [Nat.add_mul_div_left _ _ (by omega : 0 < b), Nat.div_eq_of_lt ha, zero_add]

theorem sub_top (b N : ℕ) : N - N % b = b * (N / b) := by
  have := Nat.mod_add_div N b
  omega

theorem digit_ofDigits {b : ℕ} (_hb : 2 ≤ b) (w : List ℕ)
    (hw : ∀ a ∈ w, a < b) (i : ℕ) : digit b (Nat.ofDigits b w) i = w.getD i 0 := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => simp
    | cons a w => simpa only [Nat.ofDigits_cons, List.getD_cons_zero] using
        digit_cons_zero (hw a List.mem_cons_self) (Nat.ofDigits b w)
  | succ i ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [Nat.ofDigits_cons, digit_cons_succ (hw a List.mem_cons_self)]
      exact ih w (fun a ha => hw a (List.mem_cons_of_mem _ ha))

end TapeDigits

namespace StackCode

open TapeDigits

def Represents (b : ℕ) (s : Code) (c : Configuration) : Prop :=
  s.state = c.state ∧
    (∀ i : ℕ, c.tape (c.head - 1 - (i : ℤ)) = digit b s.left i) ∧
    ∀ i : ℕ, c.tape (c.head + (i : ℤ)) = digit b s.right i

def initialCode (b : ℕ) (d : Input) : Code :=
  ⟨0, Nat.ofDigits b d.word, d.machine.start⟩

theorem initial_represents {b : ℕ} (hb : 2 ≤ b) (d : Input)
    (hw : ∀ a ∈ d.word, a < b) : Represents b (initialCode b d) (initialConfiguration d) := by
  constructor
  · rfl
  constructor
  · intro i
    simp only [initialConfiguration, initialCode, zero_sub, TapeDigits.digit_blank]
    rw [ite_eq_right (by omega)]
  · intro i
    simp only [initialConfiguration, initialCode, zero_add, Int.natCast_nonneg,
      ↓reduceIte, Int.toNat_natCast]
    exact (digit_ofDigits hb d.word hw i).symm

theorem scan_eq {b : ℕ} {s : Code} {c : Configuration} (h : Represents b s c) :
    c.tape c.head = s.right % b := by simpa only [Nat.cast_zero, add_zero, digit_zero] using h.2.2 0

theorem step_represents {b : ℕ} (hb : 2 ≤ b) {s : Code} {c : Configuration}
    {M : Machine} {I : Instruction} (h : Represents b s c)
    (hI : M.lookup c.state (c.tape c.head) = some I) (hw : I.writeSymbol < b) :
    Represents b (step b s I) (machineStep M c) := by
  have hl : s.left % b < b := Nat.mod_lt _ (by omega)
  have hm := I.move.isLt
  rw [machineStep, hI]
  dsimp only
  constructor
  · exact step_state b s I
  by_cases hR : I.move.val = 2
  · have hmove : ((I.move.val : ℤ) - 1) = 1 := by omega
    simp only [hmove, step, ite_eq_left hR]
    constructor
    · intro i
      cases i with
      | zero => simp [digit_cons_zero hw]
      | succ i =>
        have he : c.head + 1 - 1 - ((i + 1 : ℕ) : ℤ) = c.head - 1 - i := by omega
        rw [he, Function.update_of_ne (by omega), digit_cons_succ hw]
        exact h.2.1 i
    · intro i
      rw [Function.update_of_ne (by omega)]
      have he : c.head + 1 + (i : ℤ) = c.head + ((i + 1 : ℕ) : ℤ) := by omega
      rw [he, h.2.2, digit_succ]
  · by_cases hL : I.move.val = 0
    · have hmove : ((I.move.val : ℤ) - 1) = -1 := by omega
      simp only [hmove, step, ite_eq_right hR, ite_eq_left hL]
      constructor
      · intro i
        rw [Function.update_of_ne (by omega)]
        have he : c.head + -1 - 1 - (i : ℤ) = c.head - 1 - ((i + 1 : ℕ) : ℤ) := by omega
        rw [he, h.2.1, digit_succ]
      · intro i
        have hform : s.left % b + b * I.writeSymbol + b * (s.right - s.right % b) =
            s.left % b + b * (I.writeSymbol + b * (s.right / b)) := by
          rw [sub_top]; ring
        rw [hform]
        cases i with
        | zero =>
          rw [digit_cons_zero hl]
          simp only [Nat.cast_zero, add_zero]
          rw [Function.update_of_ne (by omega)]
          simpa only [Nat.cast_zero, sub_zero, sub_eq_add_neg, neg_zero, add_zero, TapeDigits.digit_zero] using h.2.1 0
        | succ i =>
          rw [digit_cons_succ hl]
          cases i with
          | zero => simp [digit_cons_zero hw]
          | succ i =>
            rw [digit_cons_succ hw, ← digit_succ]
            rw [Function.update_of_ne (by omega)]
            have he : c.head + -1 + (((i + 1) + 1 : ℕ) : ℤ) = c.head + ((i + 1 : ℕ) : ℤ) := by omega
            rw [he, h.2.2]
    · have hmove : ((I.move.val : ℤ) - 1) = 0 := by omega
      simp only [hmove, step, ite_eq_right hR, ite_eq_right hL, add_zero]
      constructor
      · intro i
        rw [Function.update_of_ne (by omega)]
        exact h.2.1 i
      · intro i
        rw [sub_top, Nat.add_comm (b * _) I.writeSymbol]
        cases i with
        | zero => simp [digit_cons_zero hw]
        | succ i =>
          rw [digit_cons_succ hw, ← digit_succ, Function.update_of_ne (by omega)]
          exact h.2.2 (i + 1)

end StackCode

namespace StackCode

open Scales

def machineStackStep (b : ℕ) (M : Machine) (s : Code) : Code :=
  (M.lookup s.state (s.right % b)).elim s (fun I => step b s I)

def stackExecution (b : ℕ) (d : Input) (n : ℕ) : Code :=
  (machineStackStep b d.machine)^[n] (initialCode b d)

@[simp] theorem stackExecution_zero (b : ℕ) (d : Input) :
    stackExecution b d 0 = initialCode b d := rfl

theorem stackExecution_succ (b : ℕ) (d : Input) (n : ℕ) :
    stackExecution b d (n + 1) = machineStackStep b d.machine (stackExecution b d n) :=
  Function.iterate_succ_apply' _ _ _

theorem stackExecution_represents {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (n : ℕ) :
    Represents b (stackExecution b d n) (execution d n) := by
  induction n with
  | zero => exact initial_represents hb d (fun a ha => (hd.2 a ha).trans_le hsymbol)
  | succ n ih =>
    have hex : execution d (n + 1) = machineStep d.machine (execution d n) :=
      Function.iterate_succ_apply' _ _ _
    rw [stackExecution_succ, hex]
    have hread : d.machine.lookup (execution d n).state ((execution d n).tape (execution d n).head) =
        d.machine.lookup (stackExecution b d n).state ((stackExecution b d n).right % b) := by
      rw [← ih.1, scan_eq ih]
    cases hI : d.machine.lookup (stackExecution b d n).state ((stackExecution b d n).right % b) with
    | none => simpa only [machineStackStep, Option.elim, hI, machineStep, hread] using ih
    | some I =>
      rw [machineStackStep, hI]
      exact step_represents hb ih (hread.trans hI)
        ((MachineFacts.lookup_bounds hd.1 hI).2.trans_le hsymbol)

theorem stackExecution_bounds {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (hstate : d.machine.states ≤ b) (n : ℕ) :
    (stackExecution b d n).left < b ^ width d.word.length n ∧
    (stackExecution b d n).right < b ^ width d.word.length n ∧
    (stackExecution b d n).state < b := by
  induction n with
  | zero =>
    dsimp only [stackExecution_zero, initialCode]
    refine ⟨pow_pos (by omega) _, ?_, hd.1.2.2.1.trans_le hstate⟩
    exact (Nat.ofDigits_lt_base_pow_length (by omega) (fun a ha => (hd.2 a ha).trans_le hsymbol)).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [width]))
  | succ n ih =>
    rw [stackExecution_succ]
    have hw : 0 < width d.word.length n := by simp [width]
    have hp : b ^ width d.word.length n ≤ b ^ width d.word.length (n + 1) := by
      apply Nat.pow_le_pow_right (by omega)
      rw [width_succ]; omega
    cases hI : d.machine.lookup (stackExecution b d n).state ((stackExecution b d n).right % b) with
    | none => simpa only [machineStackStep, Option.elim, hI] using
        And.intro (ih.1.trans_le hp) (And.intro (ih.2.1.trans_le hp) ih.2.2)
    | some I =>
      obtain ⟨hs, ha⟩ := MachineFacts.lookup_bounds hd.1 hI
      obtain ⟨hl', hr'⟩ := step_stacks_lt hb hw (stackExecution b d n) I ih.1 ih.2.1
        (ha.trans_le hsymbol)
      have hp' : b ^ (width d.word.length n + 1) ≤ b ^ width d.word.length (n + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [width_succ]; omega
      simpa only [machineStackStep, Option.elim, hI, step_state] using
        And.intro (hl'.trans_le hp') (And.intro (hr'.trans_le hp') (hs.trans_le hstate))

def configurationCode (b : ℕ) (d : Input) (n : ℕ) : ℕ :=
  pack b (width d.word.length n) (stackExecution b d n)

theorem configurationCode_bound {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (hstate : d.machine.states ≤ b) (n : ℕ) :
    configurationCode b d n < capacity b d.word.length n := by
  obtain ⟨hl, hr, hs⟩ := stackExecution_bounds hb d hd hsymbol hstate n
  exact pack_lt hb _ hl hr hs

theorem decode_configurationCode {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (hstate : d.machine.states ≤ b) (n : ℕ) :
    unpack b (width d.word.length n) (configurationCode b d n) = stackExecution b d n := by
  obtain ⟨hl, hr, hs⟩ := stackExecution_bounds hb d hd hsymbol hstate n
  exact unpack_pack hb _ hl hr hs

end StackCode

namespace RuleTable

open Scales StackCode

def halt (b L : ℕ) (M : Machine) (n : ℕ) (j : ℤ) : Bool :=
  let c := unpack b (width L n) j
  (M.lookup c.state (c.right % b)).isNone

def next (b L : ℕ) (M : Machine) (n : ℕ) (j : ℤ) : ℕ :=
  let c := unpack b (width L n) j
  (M.lookup c.state (c.right % b)).elim 0 (fun I => pack b (width L (n + 1)) (step b c I))

theorem halt_periodic (b L : ℕ) (M : Machine) (n : ℕ) :
    Function.Periodic (halt b L M n) (capacity b L n : ℤ) := by
  intro j
  simp only [halt, capacity, codeExponent, unpack_periodic b (width L n) j]

theorem next_periodic (b L : ℕ) (M : Machine) (n : ℕ) :
    Function.Periodic (next b L M n) (capacity b L n : ℤ) := by
  intro j
  simp only [next, capacity, codeExponent, unpack_periodic b (width L n) j]

theorem next_bound {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (M : Machine) (hM : M.WellFormed)
    (hsymbol : M.symbols ≤ b) (hstate : M.states ≤ b) (n : ℕ) (j : ℤ) :
    next b L M n j < capacity b L (n + 1) := by
  have hp : 0 < b ^ width L n := pow_pos (by omega) _
  have hl : (unpack b (width L n) j).left < b ^ width L n := Nat.mod_lt _ hp
  have hr : (unpack b (width L n) j).right < b ^ width L n := Nat.mod_lt _ hp
  unfold next
  dsimp only
  unfold Option.elim
  split
  · rename_i I hI
    obtain ⟨hs, ha⟩ := MachineFacts.lookup_bounds hM hI
    simpa only [capacity, codeExponent, width_succ] using
      step_pack_lt hb (show 0 < width L n by simp [width]) _ I hl hr
        (ha.trans_le hsymbol) (hs.trans_le hstate)
  · exact pow_pos (by omega) _

theorem halt_code {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (hstate : d.machine.states ≤ b) (n : ℕ) :
    halt b d.word.length d.machine n (configurationCode b d n) =
      (d.machine.lookup (execution d n).state ((execution d n).tape (execution d n).head)).isNone := by
  have hrep := stackExecution_represents hb d hd hsymbol n
  simp only [halt, decode_configurationCode hb d hd hsymbol hstate, hrep.1, scan_eq hrep]

theorem next_code {b : ℕ} (hb : 2 ≤ b) (d : Input) (hd : d.WellFormed)
    (hsymbol : d.machine.symbols ≤ b) (hstate : d.machine.states ≤ b) (n : ℕ)
    (hn : halt b d.word.length d.machine n (configurationCode b d n) = false) :
    next b d.word.length d.machine n (configurationCode b d n) = configurationCode b d (n + 1) := by
  simp only [halt, decode_configurationCode hb d hd hsymbol hstate] at hn
  simp only [next, decode_configurationCode hb d hd hsymbol hstate]
  rw [configurationCode, stackExecution_succ]
  unfold machineStackStep
  cases hI : d.machine.lookup (stackExecution b d n).state ((stackExecution b d n).right % b) with
  | none => simp only [hI, Option.isNone_none, Bool.true_eq_false] at hn
  | some I => rfl

end RuleTable

namespace Planar

theorem codes_prefix (F : ℕ → ℤ → ℕ) (H : ℕ → ℤ → Bool) (s : ℕ → ℕ)
    (hstep : ∀ n, H n (s n) = false → F n (s n) = s (n + 1)) (n : ℕ)
    (hprevious : ∀ k < n, H k (s k) = false) : codes F (s 0) n = s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun k hk => hprevious k (Nat.lt_succ_of_lt hk))
    rw [codes, hi, hstep n (hprevious n (Nat.lt_succ_self n))]

theorem codes_flag_iff (F : ℕ → ℤ → ℕ) (H : ℕ → ℤ → Bool) (s : ℕ → ℕ)
    (hstep : ∀ n, H n (s n) = false → F n (s n) = s (n + 1)) :
    (∃ n, H n (codes F (s 0) n) = true) ↔ ∃ n, H n (s n) = true := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra hfalse
    have ha : ∀ k, H k (s k) = false := fun k =>
      Bool.eq_false_iff.mpr (fun hk => hfalse ⟨k, hk⟩)
    rw [codes_prefix F H s hstep n (fun k _ => ha k), ha] at hn
    contradiction
  · intro htrue
    let n := Nat.find htrue
    have hn := Nat.find_spec htrue
    refine ⟨n, ?_⟩
    rw [codes_prefix F H s hstep n (fun k hk => Bool.eq_false_iff.mpr (Nat.find_min htrue hk))]
    exact hn

end Planar

end
end PeriodicLattice

end OAI
