import OAI.MathematicalPhysics.RapidForcing.Profiles

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

def radix (A p : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, f i * A ^ i

lemma radix_lt {A p : ℕ} {f : ℕ → ℕ} (hA : 0 < A)
    (hf : ∀ i < p, f i < A) : radix A p f < A ^ p := by
  induction p with
  | zero => simp [radix]
  | succ p ih =>
    have hs := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hp := hf p (Nat.lt_succ_self p)
    have hpow : 0 < A ^ p := pow_pos hA _
    simp only [radix, Finset.sum_range_succ, pow_succ] at *
    nlinarith

lemma radix_digit {A p j : ℕ} {f : ℕ → ℕ} (hA : 0 < A)
    (hf : ∀ i < p, f i < A) (hj : j < p) :
    radix A p f / A ^ j % A = f j := by
  induction p with
  | zero => omega
  | succ p ih =>
    have he : radix A (p + 1) f = radix A p f + f p * A ^ p :=
      Finset.sum_range_succ _ _
    rw [he]
    have hjp : j ≤ p := by omega
    have hfac : A ^ p = A ^ j * A ^ (p - j) := by
      rw [← pow_add, Nat.add_sub_of_le hjp]
    rw [hfac, ← mul_assoc, mul_comm (f p) (A ^ j), mul_assoc,
      Nat.add_mul_div_left _ _ (pow_pos hA _)]
    by_cases hj' : j < p
    · rw [Nat.add_mod, ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)) hj']
      have hd : A ∣ A ^ (p - j) := dvd_pow_self _ (by omega)
      rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd _), add_zero,
        Nat.mod_eq_of_lt (hf j (Nat.lt_succ_of_lt hj'))]
    · have hje : j = p := by omega
      subst j
      have hp := radix_lt hA (fun i hi => hf i (Nat.lt_succ_of_lt hi))
      simp [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt (hf p (Nat.lt_succ_self p))]

lemma radix_update {A p j : ℕ} (f : ℕ → ℕ) (z : ℕ) (hj : j < p) :
    radix A p (Function.update f j z) = radix A p f - f j * A ^ j + z * A ^ j := by
  classical
  have he : radix A p f = (∑ i ∈ (Finset.range p).erase j, f i * A ^ i) + f j * A ^ j :=
    (Finset.sum_erase_add _ _ (Finset.mem_range.mpr hj)).symm
  have hu : radix A p (Function.update f j z) =
      (∑ i ∈ (Finset.range p).erase j, f i * A ^ i) + z * A ^ j := by
    unfold radix
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hj)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hu, he, Nat.add_sub_cancel_right]

lemma radix_eq_ofDigits (A : ℕ) (l : List ℕ) :
    radix A l.length (fun i => l.getD i 0) = Nat.ofDigits A l := by
  induction l with
  | nil => simp [radix]
  | cons a l ih =>
    simp only [List.length_cons, radix, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, add_comm]
    change a + radix A l.length (fun i => l.getD i 0) * A = _
    rw [ih]
    simp [Nat.ofDigits, mul_comm]

lemma radix_expand (A p : ℕ) (f : ℕ → ℕ) (h0 : f 0 = 0) (hp : f (p + 1) = 0) :
    radix A (p + 2) f = A * radix A p (fun i => f (i + 1)) := by
  rw [radix, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [h0, hp, zero_mul, add_zero, pow_succ, ← mul_assoc]
  rw [← Finset.sum_mul, mul_comm]
  rfl

namespace Machine
variable (M : Machine)

def ValidAt (B n : ℕ) (c : M.Config) : Prop :=
  -(n : ℤ) ≤ c.head ∧ c.head ≤ (n : ℤ) ∧
    ∀ i : ℤ, i < -(n : ℤ) ∨ (n : ℤ) + B < i → c.tape i = M.blank

def tapeCode (w : M.Input) (n : ℕ) (c : M.Config) : ℕ :=
  radix (M.scaleData w).A (2 * n + w.length + 1)
    (fun i => (c.tape ((i : ℤ) - n)).val)

def configCode (w : M.Input) (n : ℕ) (c : M.Config) : ℕ :=
  c.state.val + (M.scaleData w).S * ((c.head + (n : ℤ)).toNat +
    (M.scaleData w).P n * M.tapeCode w n c)

lemma initialConfig_valid (w : M.Input) : M.ValidAt w.length 0 (M.initialConfig w) := by
  refine ⟨by simp [initialConfig], by simp [initialConfig], ?_⟩
  intro i hi
  simp only [initialConfig]
  split_ifs with h
  · have : w.length ≤ i.toNat := by omega
    simp [List.getElem?_eq_none this]
  · rfl

lemma nextConfig_head_bounds (c : M.Config) :
    c.head - 1 ≤ (M.nextConfig c).head ∧ (M.nextConfig c).head ≤ c.head + 1 := by
  unfold nextConfig
  split_ifs
  · split
    · simp
    · rename_i v h
      have := v.isLt
      dsimp
      omega
  · simp

lemma nextConfig_tape_of_ne (c : M.Config) {i : ℤ} (hi : i ≠ c.head) :
    (M.nextConfig c).tape i = c.tape i := by
  unfold nextConfig
  split_ifs
  · split
    · rfl
    · simp [Function.update_of_ne hi]
  · rfl

lemma nextConfig_preserves_blanks {B n : ℕ} {c : M.Config} (hc : M.ValidAt B n c)
    {i : ℤ} (hi : i < -(n : ℤ) ∨ (n : ℤ) + B < i) :
    (M.nextConfig c).tape i = M.blank := by
  rw [M.nextConfig_tape_of_ne c (by rcases hc with ⟨h1, h2, _⟩; omega)]
  exact hc.2.2 i hi

lemma nextConfig_valid {B n : ℕ} {c : M.Config} (hc : M.ValidAt B n c) :
    M.ValidAt B (n + 1) (M.nextConfig c) := by
  have hh := M.nextConfig_head_bounds c
  refine ⟨by have := hc.1; push_cast; omega, by have := hc.2.1; push_cast; omega, ?_⟩
  intro i hi
  apply M.nextConfig_preserves_blanks hc
  push_cast at hi
  omega

lemma run_succ (w : M.Input) (n : ℕ) : M.run w (n + 1) = M.nextConfig (M.run w n) := by
  exact Function.iterate_succ_apply' _ _ _

lemma run_valid (w : M.Input) (n : ℕ) : M.ValidAt w.length n (M.run w n) := by
  induction n with
  | zero => exact M.initialConfig_valid w
  | succ n ih => rw [M.run_succ]; exact M.nextConfig_valid ih

lemma headIndex_bounds {B n : ℕ} {c : M.Config} (hc : M.ValidAt B n c) :
    ((c.head + (n : ℤ)).toNat : ℤ) = c.head + n ∧ (c.head + (n : ℤ)).toNat ≤ 2 * n := by
  have h1 := hc.1
  have h2 := hc.2.1
  constructor
  · exact Int.toNat_of_nonneg (by omega)
  · omega

lemma tapeCode_lt (w : M.Input) (n : ℕ) (c : M.Config) :
    M.tapeCode w n c < (M.scaleData w).A ^ (2 * n + w.length + 1) := by
  apply radix_lt (M.scaleData w).A_pos
  intro i _
  exact lt_trans (c.tape _).isLt (M.alphabet_lt_A w)

lemma configCode_lt (w : M.Input) {n : ℕ} {c : M.Config} (hc : M.ValidAt w.length n c) :
    M.configCode w n c < (M.scaleData w).capacity n := by
  let d := M.scaleData w
  have hq : c.state.val < d.S := lt_of_le_of_lt (by omega) (M.states_lt_S w)
  have hj : (c.head + (n : ℤ)).toNat < d.P n :=
    lt_of_le_of_lt (M.headIndex_bounds hc).2 (d.head_lt_P n)
  rw [d.capacity_eq]
  simpa only [configCode, mul_assoc, d, scaleData] using
    (radix_pair_lt hq (radix_pair_lt hj (M.tapeCode_lt w n c)))

lemma configCode_read (w : M.Input) {n : ℕ} {c : M.Config} (hc : M.ValidAt w.length n c) :
    let d := M.scaleData w
    let k := M.configCode w n c
    k % d.S = c.state.val ∧
    (k / d.S) % d.P n = (c.head + (n : ℤ)).toNat ∧
    k / (d.S * d.P n) = M.tapeCode w n c := by
  let d := M.scaleData w
  have hq : c.state.val < d.S := lt_of_le_of_lt (by omega) (M.states_lt_S w)
  have hj : (c.head + (n : ℤ)).toNat < d.P n :=
    lt_of_le_of_lt (M.headIndex_bounds hc).2 (d.head_lt_P n)
  change (c.state.val + d.S * _) % d.S = _ ∧ _
  constructor
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hq]
  dsimp [configCode]
  rw [Nat.add_mul_div_left _ _ d.S_pos, Nat.div_eq_of_lt hq, zero_add]
  constructor
  · change ((c.head + (n : ℤ)).toNat + d.P n * _) % d.P n = _
    simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ d.S_pos,
    Nat.div_eq_of_lt hq, zero_add, Nat.add_mul_div_left _ _ (d.P_pos n),
    Nat.div_eq_of_lt hj, zero_add]

lemma tapeCode_read (w : M.Input) {n : ℕ} {c : M.Config} (hc : M.ValidAt w.length n c) :
    let d := M.scaleData w
    M.tapeCode w n c / d.A ^ (c.head + (n : ℤ)).toNat % d.A = (c.tape c.head).val := by
  have hj := M.headIndex_bounds hc
  dsimp only
  unfold tapeCode
  rw [radix_digit (f := fun i => (c.tape ((i : ℤ) - n)).val) (M.scaleData w).A_pos
    (fun i _ => lt_trans (c.tape _).isLt (M.alphabet_lt_A w)) (by omega), hj.1]
  simp

lemma nextConfig_instruction {c : M.Config} (hc : c.state.val < M.states) :
    let ins := M.instruction c.state.val (c.tape c.head).val
    (M.nextConfig c).state.val = ins.1 ∧
    (M.nextConfig c).head = c.head + (ins.2.2.val : ℤ) - 1 ∧
    ∀ i : ℤ, ((M.nextConfig c).tape i).val =
      Function.update (fun l => (c.tape l).val) c.head ins.2.1 i := by
  unfold nextConfig instruction
  rw [dite_eq_left hc, dite_eq_left hc, dite_eq_left (c.tape c.head).isLt]
  simp only [Fin.eta]
  cases htr : M.transition ⟨c.state.val, hc⟩ (c.tape c.head) with
  | none => simp
  | some v =>
    rcases v with ⟨q, z, d⟩
    refine ⟨rfl, rfl, ?_⟩
    intro i
    simp only [Function.update_apply]
    split_ifs <;> rfl

lemma tapeCode_extend (w : M.Input) {n : ℕ} {c : M.Config} (hc : M.ValidAt w.length n c) :
    M.tapeCode w (n + 1) (M.nextConfig c) = (M.scaleData w).A *
      radix (M.scaleData w).A (2 * n + w.length + 1)
        (fun i => ((M.nextConfig c).tape ((i : ℤ) - n)).val) := by
  have hlen : 2 * (n + 1) + w.length + 1 = (2 * n + w.length + 1) + 2 := by omega
  have h0 : (M.nextConfig c).tape ((0 : ℤ) - (n + 1 : ℕ)) = M.blank :=
    M.nextConfig_preserves_blanks hc (Or.inl (by push_cast; omega))
  have hp : (M.nextConfig c).tape (((2 * n + w.length + 1 + 1 : ℕ) : ℤ) - (n + 1 : ℕ)) = M.blank :=
    M.nextConfig_preserves_blanks hc (Or.inr (by push_cast; omega))
  unfold tapeCode
  rw [hlen, radix_expand _ _ _ (by simp only [Nat.cast_zero]; rw [h0]; rfl) (by rw [hp]; rfl)]
  congr 2
  funext i
  congr 2
  push_cast
  ring

lemma tapeCode_next (w : M.Input) {n : ℕ} {c : M.Config}
    (hc : M.ValidAt w.length n c) (hq : c.state.val < M.states) :
    let ins := M.instruction c.state.val (c.tape c.head).val
    let j := (c.head + (n : ℤ)).toNat
    M.tapeCode w (n + 1) (M.nextConfig c) = (M.scaleData w).A *
      (M.tapeCode w n c - (c.tape c.head).val * (M.scaleData w).A ^ j +
        ins.2.1 * (M.scaleData w).A ^ j) := by
  dsimp only
  rw [M.tapeCode_extend w hc]
  have he : (fun i : ℕ => ((M.nextConfig c).tape ((i : ℤ) - n)).val) =
      Function.update (fun i : ℕ => (c.tape ((i : ℤ) - n)).val)
        (c.head + (n : ℤ)).toNat (M.instruction c.state.val (c.tape c.head).val).2.1 := by
    funext i
    rw [(M.nextConfig_instruction hq).2.2]
    simp only [Function.update_apply]
    have hj := (M.headIndex_bounds hc).1
    by_cases hi : i = (c.head + (n : ℤ)).toNat
    · subst i
      simp [hj]
    · have hi' : (i : ℤ) - n ≠ c.head := by omega
      simp [hi, hi']
  rw [he, radix_update _ _ (by have := (M.headIndex_bounds hc).2; omega),
    (M.headIndex_bounds hc).1]
  simp only [add_sub_cancel_right]
  rfl

theorem nextDigit_configCode (w : M.Input) {n : ℕ} {c : M.Config}
    (hc : M.ValidAt w.length n c) (hq : c.state.val < M.states) :
    M.nextDigit (M.scaleData w) n (M.configCode w n c) =
      M.configCode w (n + 1) (M.nextConfig c) := by
  have hr := M.configCode_read w hc
  have hnext := M.nextConfig_instruction hq
  have hj := M.headIndex_bounds hc
  have hj' : ((M.nextConfig c).head + ((n + 1 : ℕ) : ℤ)).toNat =
      (c.head + (n : ℤ)).toNat + (M.instruction c.state.val (c.tape c.head).val).2.2.val := by
    rw [hnext.2.1]
    push_cast
    omega
  unfold nextDigit
  dsimp only
  rw [hr.1, hr.2.1, hr.2.2, M.tapeCode_read w hc]
  rw [ite_eq_left ⟨hq, hj.2, (c.tape c.head).isLt⟩]
  unfold configCode
  rw [hnext.1, hj', M.tapeCode_next w hc hq]
  ring

lemma terminalDigit_configCode (w : M.Input) {n : ℕ} {c : M.Config}
    (hc : M.ValidAt w.length n c) :
    M.terminalDigit (M.scaleData w) (M.configCode w n c) =
      if c.state.val = M.states then 1 else 0 := by
  unfold terminalDigit
  rw [(M.configCode_read w hc).1]

lemma initialConfig_tape_val (w : M.Input) (i : ℕ) :
    ((M.initialConfig w).tape (i : ℤ)).val = (w.map Fin.val).getD i 0 := by
  by_cases hi : i < w.length
  · simp [initialConfig, Nat.cast_nonneg, hi, List.getD_eq_getElem?_getD]
  · have hi' : w.length ≤ i := by omega
    simp [initialConfig, Nat.cast_nonneg, List.getElem?_eq_none hi',
      List.getD_eq_getElem?_getD, blank]

lemma configCode_initial (w : M.Input) :
    M.configCode w 0 (M.initialConfig w) = M.initialDigit w := by
  rw [M.initialDigit_eq]
  have hT : M.tapeCode w 0 (M.initialConfig w) = Nat.ofDigits (M.scaleData w).A (w.map Fin.val) := by
    unfold tapeCode
    simp only [mul_zero, zero_add, Nat.cast_zero, sub_zero]
    rw [radix, Finset.sum_range_succ]
    simp only [M.initialConfig_tape_val]
    have hz : (w.map Fin.val).getD w.length 0 = 0 := by simp [List.getD_eq_getElem?_getD]
    rw [hz, zero_mul, add_zero]
    simpa only [radix, List.length_map] using radix_eq_ofDigits (M.scaleData w).A (w.map Fin.val)
  unfold configCode
  rw [hT]
  simp [initialConfig]

def runCode (w : M.Input) (n : ℕ) : ℕ := M.configCode w n (M.run w n)

lemma runCode_lt (w : M.Input) (n : ℕ) : M.runCode w n < (M.scaleData w).capacity n :=
  M.configCode_lt w (M.run_valid w n)

lemma runCode_zero (w : M.Input) : M.runCode w 0 = M.initialDigit w :=
  M.configCode_initial w

lemma runCode_succ (w : M.Input) {n : ℕ} (hn : (M.run w n).state.val ≠ M.states) :
    M.runCode w (n + 1) = M.nextDigit (M.scaleData w) n (M.runCode w n) := by
  unfold runCode
  rw [M.run_succ]
  exact (M.nextDigit_configCode w (M.run_valid w n) (by have := (M.run w n).state.isLt; omega)).symm

lemma runCode_terminal (w : M.Input) (n : ℕ) :
    M.terminalDigit (M.scaleData w) (M.runCode w n) =
      if (M.run w n).state.val = M.states then 1 else 0 :=
  M.terminalDigit_configCode w (M.run_valid w n)

end Machine
end RapidForcing

end OAI
