import OAI.MathematicalPhysics.AlternatingFlow.Profiles

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Machine

def Admissible (M : Machine) (c : Configuration) : Prop :=
  c.state ≤ M.states ∧ ∀ i, c.tape i < M.alphabet

def command (M : Machine) (q a : ℕ) : Rule :=
  letI := neZeroThree
  if q = M.states ∨ q ∈ M.haltingStates then (q, a, 1)
  else (M.instruction q a).getD (M.states, a, 1)

lemma step_eq_command (M : Machine) (c : Configuration) :
    M.step c =
      { state := (M.command c.state (c.tape c.head)).1
        head := c.head + (((M.command c.state (c.tape c.head)).2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head (M.command c.state (c.tape c.head)).2.1 } := by
  unfold step isHalting command
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp [Function.update_eq_self]
  · cases M.instruction c.state (c.tape c.head) <;> simp [Function.update_eq_self]

lemma command_valid (M : Machine) (hM : M.WellFormed) (q a : ℕ)
    (hq : q ≤ M.states) (ha : a < M.alphabet) :
    (M.command q a).1 ≤ M.states ∧ (M.command q a).2.1 < M.alphabet := by
  unfold command
  split_ifs with h
  · exact ⟨hq, ha⟩
  · cases hc : M.instruction q a with
    | none => simp [ha]
    | some r =>
      have hr := hM.2.2 q a r (lt_of_le_of_ne hq (by tauto)) ha hc
      exact ⟨hr.1.le, hr.2⟩

lemma initial_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) : M.Admissible (M.initial w) := by
  refine ⟨hM.1.le, ?_⟩
  intro i
  dsimp [initial]
  split_ifs
  · cases h : w[i.toNat]? with
    | none => simp [alphabet]
    | some a => exact hw a (List.mem_of_getElem? h)
  · simp [alphabet]

lemma step_admissible (M : Machine) (hM : M.WellFormed) (c : Configuration)
    (hc : M.Admissible c) : M.Admissible (M.step c) := by
  rw [step_eq_command]
  have hr := command_valid M hM c.state (c.tape c.head) hc.1 (hc.2 c.head)
  refine ⟨hr.1, ?_⟩
  intro i
  dsimp
  by_cases hi : i = c.head
  · subst i; simpa using hr.2
  · simpa [Function.update_of_ne hi] using hc.2 i

lemma run_zero (M : Machine) (w : List ℕ) : M.run w 0 = M.initial w := rfl

lemma run_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    M.run w (n + 1) = M.step (M.run w n) :=
  Function.iterate_succ_apply' _ _ _

lemma run_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) : M.Admissible (M.run w n) := by
  induction n with
  | zero => exact initial_admissible M hM w hw
  | succ n ih => rw [run_succ]; exact step_admissible M hM _ ih

def Window (N n : ℕ) (c : Configuration) : Prop :=
  -(n : ℤ) ≤ c.head ∧ c.head ≤ n ∧
    ∀ i : ℤ, (i < -(n : ℤ) ∨ (N : ℤ) + n ≤ i) → c.tape i = 0

lemma initial_window (M : Machine) (w : List ℕ) : Window w.length 0 (M.initial w) := by
  refine ⟨by simp [initial], by simp [initial], ?_⟩
  intro i hi
  dsimp [initial]
  by_cases h : 0 ≤ i
  · rw [ite_eq_left h, List.getElem?_eq_none (by omega)]
    rfl
  · simp [h]

lemma step_window (M : Machine) (N n : ℕ) (c : Configuration)
    (hc : Window N n c) : Window N (n + 1) (M.step c) := by
  rw [step_eq_command]
  have hd := (M.command c.state (c.tape c.head)).2.2.isLt
  rcases hc with ⟨hl, hu, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp; omega
  · dsimp; omega
  · intro i hi
    have hi' : i ≠ c.head := by omega
    have hblank := ht i (by omega)
    simpa [Function.update_of_ne hi'] using hblank

lemma run_window (M : Machine) (w : List ℕ) (n : ℕ) :
    Window w.length n (M.run w n) := by
  induction n with
  | zero => exact initial_window M w
  | succ n ih => rw [run_succ]; exact step_window M w.length n _ ih

def leftDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head - (j + 1))
def rightDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head + j)

lemma leftDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : leftDigits c j = 0 := by
  unfold leftDigits
  have hh := hc.2.1
  rw [hc.2.2 _ (Or.inl (by dsimp [Scales.K] at hj; omega))]

lemma rightDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : rightDigits c j = 0 := by
  unfold rightDigits
  have hh := hc.1
  rw [hc.2.2 _ (Or.inr (by dsimp [Scales.K] at hj; omega))]

def base (M : Machine) : ℕ := 2 * (1 + max (M.states + 1) M.alphabet)

lemma base_ge_four (M : Machine) : 4 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base, states] at *
  omega

lemma state_digit_bound (M : Machine) (q : ℕ) (hq : q ≤ M.states) :
    2 * q + 2 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base]
  omega

lemma symbol_digit_bound (M : Machine) (a : ℕ) (ha : a < M.alphabet) :
    2 * a + 2 ≤ M.base := by
  have h := le_max_right (M.states + 1) M.alphabet
  dsimp [base]
  omega

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Encoding

def digits (K : ℕ) (f : ℕ → ℕ) : List ℕ := List.ofFn (fun i : Fin K => f i)

noncomputable def streamCode (b K : ℕ) (f : ℕ → ℕ) : ℝ := code b (digits K f)

lemma digits_length (K : ℕ) (f : ℕ → ℕ) : (digits K f).length = K := by
  simp [digits]

lemma digits_succ (K : ℕ) (f : ℕ → ℕ) :
    digits (K + 1) f = f 0 :: digits K (fun j => f (j + 1)) :=
  List.ofFn_succ

lemma streamCode_succ (b K : ℕ) (f : ℕ → ℕ) :
    streamCode b (K + 1) f = ((f 0 : ℝ) + streamCode b K (fun j => f (j + 1))) / b := by
  simp only [streamCode, digits_succ, code]

lemma streamCode_congr (b K : ℕ) (f g : ℕ → ℕ) (h : ∀ j < K, f j = g j) :
    streamCode b K f = streamCode b K g := by
  have hl : digits K f = digits K g :=
    congrArg List.ofFn (funext (fun j : Fin K => h j j.isLt))
  exact congrArg (code b) hl

lemma streamCode_extend_one (b K : ℕ) (hb : 0 < b) (f : ℕ → ℕ) (hK : f K = 0) :
    streamCode b (K + 1) f = streamCode b K f := by
  unfold streamCode digits
  rw [List.ofFn_succ', List.concat_eq_append]
  change code b (List.ofFn (fun i : Fin K => f i) ++ [f K]) = _
  rw [code_append b hb]
  simp [hK, code]

lemma streamCode_padding (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L) (f : ℕ → ℕ)
    (hf : ∀ j, K ≤ j → f j = 0) : streamCode b L f = streamCode b K f := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hL ih => rw [streamCode_extend_one b L hb f (hf L hL), ih]

lemma streamCode_pop (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L + 1)
    (f : ℕ → ℕ) (hf : ∀ j, K ≤ j → f j = 0) :
    streamCode b L (fun j => f (j + 1)) = (b : ℝ) * streamCode b K f - f 0 := by
  have h := streamCode_succ b L f
  rw [streamCode_padding b K (L + 1) hb hKL f hf] at h
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  apply (eq_div_iff hb').1 at h
  linarith

end Encoding

namespace Machine

noncomputable def leftCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (leftDigits c)

noncomputable def rightCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (rightDigits c)

def recordedDigits (M : Machine) (w : List ℕ) (n : ℕ) : List ℕ :=
  let c := M.run w n
  2 * c.state :: (Encoding.digits (Scales.K w.length n) (leftDigits c) ++
    Encoding.digits (Scales.K w.length n) (rightDigits c))

noncomputable def recordedBlock (M : Machine) (w : List ℕ) (n : ℕ) : ℝ :=
  Encoding.code M.base (M.recordedDigits w n)

lemma recordedDigits_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    ∀ d ∈ M.recordedDigits w n, d + 2 ≤ M.base := by
  have hc := run_admissible M hM w hw n
  intro d hd
  simp only [recordedDigits, Encoding.digits, List.mem_cons, List.mem_append,
    List.mem_ofFn] at hd
  rcases hd with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact state_digit_bound M _ hc.1
  · exact symbol_digit_bound M _ (hc.2 _)
  · exact symbol_digit_bound M _ (hc.2 _)

lemma recordedBlock_mem (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    M.recordedBlock w n ∈ Set.Icc (0 : ℝ) (Encoding.tailMax M.base) :=
  ⟨Encoding.code_nonneg _ _, Encoding.code_le_tailMax _ (by have := base_ge_four M; omega)
    _ (recordedDigits_bound M hM w hw n)⟩

lemma recordedBlock_formula (M : Machine) (w : List ℕ) (n : ℕ) :
    M.recordedBlock w n =
      ((2 * (M.run w n).state : ℕ) + leftCode M.base w.length n (M.run w n) +
        ((M.base : ℝ) ^ Scales.K w.length n)⁻¹ *
          rightCode M.base w.length n (M.run w n)) / M.base := by
  unfold recordedBlock recordedDigits leftCode rightCode Encoding.streamCode
  rw [Encoding.configuration_block _ _ (by have := base_ge_four M; omega),
    Encoding.digits_length]

lemma recordedBlock_integral (M : Machine) (w : List ℕ) (n : ℕ) :
    ∃ a : ℤ, (M.base : ℝ) ^ (1 + 2 * Scales.K w.length n) * M.recordedBlock w n = a := by
  obtain ⟨a, ha⟩ := Encoding.code_denominator M.base (by have := base_ge_four M; omega)
    (M.recordedDigits w n)
  refine ⟨a, ?_⟩
  have hlen : (M.recordedDigits w n).length = 1 + 2 * Scales.K w.length n := by
    simp only [recordedDigits, List.length_cons, List.length_append, Encoding.digits_length]
    omega
  simpa only [recordedBlock, hlen, Int.cast_natCast] using ha

lemma read_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) :
    let b := M.base
    let s := Scales.s w.length n
    let K := Scales.K w.length n
    let D := Encoding.donor b w.length (M.recordedBlock w) n
    Profiles.decoder b ((b : ℝ) ^ s * D) = M.recordedBlock w n ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = rightCode b w.length n (M.run w n) ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ K)⁻¹ *
      Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = leftCode b w.length n (M.run w n) :=
  Encoding.read_donor_configuration M.base w.length n (by have := base_ge_four M; omega)
    (fun j => 2 * (M.run w j).state)
    (fun j => Encoding.digits (Scales.K w.length j) (leftDigits (M.run w j)))
    (fun j => Encoding.digits (Scales.K w.length j) (rightDigits (M.run w j)))
    (fun j => Encoding.digits_length _ _) (fun j => Encoding.digits_length _ _)
    (recordedDigits_bound M hM w hw)

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Machine

def execute (c : Configuration) (r : Rule) : Configuration where
  state := r.1
  head := c.head + ((r.2.2.val : ℤ) - 1)
  tape := Function.update c.tape c.head r.2.1

lemma step_execute (M : Machine) (c : Configuration) :
    M.step c = execute c (M.command c.state (c.tape c.head)) := step_eq_command M c

lemma execute_right (c : Configuration) (r : Rule) (hd : r.2.2 = 2) :
    leftDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, leftDigits (execute c r) (j + 1) = leftDigits c j) ∧
    (∀ j, rightDigits (execute c r) j = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [leftDigits, execute, hd]
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 - ((j : ℤ) + 1 + 1) = c.head - ((j : ℤ) + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 + (j : ℤ) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma execute_stay (c : Configuration) (r : Rule) (hd : r.2.2 = 1) :
    (∀ j, leftDigits (execute c r) j = leftDigits c j) ∧
    rightDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    simp [leftDigits, execute, hd, Function.update_of_ne hi]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    simp [rightDigits, execute, hd, Function.update_of_ne hi]

lemma execute_left (c : Configuration) (r : Rule) (hd : r.2.2 = 0) :
    (∀ j, leftDigits (execute c r) j = leftDigits c (j + 1)) ∧
    rightDigits (execute c r) 0 = leftDigits c 0 ∧
    rightDigits (execute c r) 1 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1 + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1 + 1) ≠ c.head := by omega
    have he : c.head + (-1) - ((j : ℤ) + 1) = c.head - ((j : ℤ) + 1 + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · simp [leftDigits, rightDigits, execute, hd, sub_eq_add_neg]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + (-1) + ((j : ℤ) + 1 + 1) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma code_execute_right (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 2) :
    leftCode b N (n + 1) (execute c r) = ((2 * r.2.1 : ℕ) + leftCode b N n c) / b ∧
    rightCode b N (n + 1) (execute c r) =
      (b : ℝ) * rightCode b N n c - rightDigits c 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_right c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [hK, Encoding.streamCode_succ, h₀]
    have he : (fun j => leftDigits (execute c r) (j + 1)) = leftDigits c := funext h₁
    rw [he, Encoding.streamCode_padding b (Scales.K N n) (Scales.K N n + 1) hb
      (by omega) _ (leftDigits_padded N n c hc)]
  · unfold rightCode
    rw [show rightDigits (execute c r) = (fun j => rightDigits c (j + 1)) from funext h₂]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (rightDigits_padded N n c hc)

lemma code_execute_stay (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 1) :
    leftCode b N (n + 1) (execute c r) = leftCode b N n c ∧
    rightCode b N (n + 1) (execute c r) =
      ((2 * r.2.1 : ℕ) + ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_stay c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [show leftDigits (execute c r) = leftDigits c from funext h₀]
    exact Encoding.streamCode_padding b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, h₁, funext h₂]
    rw [Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n + 1) hb (by omega) _
      (rightDigits_padded N n c hc)]

lemma code_execute_left (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 0) :
    leftCode b N (n + 1) (execute c r) =
      (b : ℝ) * leftCode b N n c - leftDigits c 0 ∧
    rightCode b N (n + 1) (execute c r) =
      ((leftDigits c 0 : ℝ) + ((2 * r.2.1 : ℕ) +
        ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b) / b := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := execute_left c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [funext h₀]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, Encoding.streamCode_succ]
    simp only [h₁, zero_add, h₂]
    rw [funext h₃, Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n) hb (by omega) _
      (rightDigits_padded N n c hc)]

end Machine
end AlternatingNS

end OAI
