import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ApproximateBisection
import OAI.Computability.QuantumFactoring.BitStackRationals

namespace OAI

/-! Common-denominator registers for approximate bisection.  Each update
doubles the denominator and uses only addition and doubling of numerators;
therefore every register gains at most one bit per iteration. -/

namespace ContinuumCoulomb.BisectionRegisters
open ExactQuantumFactoring.BitStackProgram

abbrev Registers := ℤ × (ℤ × (ℕ × Bool))

def code : Registers → List Bool :=
  prodCode intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))

def left (r : Registers) : ℚ := mkRat r.1 r.2.2.1
def right (r : Registers) : ℚ := mkRat r.2.1 r.2.2.1
def middle (r : Registers) : ℚ := mkRat (r.1 + r.2.1) (2 * r.2.2.1)

def interval (r : Registers) : ApproximateBisection.Interval :=
  ⟨left r, right r, r.2.2.2⟩

def step (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) : Registers :=
  if r.2.2.2 then r
  else if δ < evaluate (middle r) then
    (r.1 + r.2.1, (2 * r.2.1, (2 * r.2.2.1, false)))
  else if evaluate (middle r) < -δ then
    (2 * r.1, (r.1 + r.2.1, (2 * r.2.2.1, false)))
  else (r.1 + r.2.1, (r.1 + r.2.1, (2 * r.2.2.1, true)))

def initial (a b : ℚ) : Registers :=
  (a.num * b.den, (b.num * a.den, (a.den * b.den, false)))

theorem initial_den_pos (a b : ℚ) : 0 < (initial a b).2.2.1 :=
  Nat.mul_pos a.pos b.pos

theorem middle_eq (r : Registers) (hr : 0 < r.2.2.1) :
    middle r = ApproximateBisection.midpoint (interval r) := by
  have hd : (r.2.2.1 : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [middle, ApproximateBisection.midpoint, interval, left, right,
    Rat.mkRat_eq_div, Int.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem initial_interval (a b : ℚ) :
    interval (initial a b) = ApproximateBisection.initial a b := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have hl : left (initial a b) = a := by
    change mkRat (a.num * b.den) (a.den * b.den) = a
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den a]
    field_simp
  have hh : right (initial a b) = b := by
    change mkRat (b.num * a.den) (a.den * b.den) = b
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den b]
    field_simp
  change (⟨left (initial a b), right (initial a b), false⟩ :
    ApproximateBisection.Interval) = ⟨a, b, false⟩
  rw [hl, hh]

theorem step_den_pos (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : 0 < (step δ evaluate r).2.2.1 := by
  unfold step
  split_ifs <;> first | exact hr | exact Nat.mul_pos (by decide) hr

private theorem double_quotient (z : ℤ) (d : ℕ) (hd : 0 < d) :
    mkRat (2 * z) (2 * d) = mkRat z d := by
  have h : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Rat.mkRat_eq_div, Int.cast_mul, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem step_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : interval (step δ evaluate r) =
      ApproximateBisection.step δ evaluate (interval r) := by
  have hm : middle r = (left r + right r) / 2 := middle_eq r hr
  unfold step ApproximateBisection.step
  simp only [interval, ApproximateBisection.midpoint, ← hm]
  split_ifs <;> simp [left, right, middle, double_quotient, hr]

theorem iterate_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) (n : ℕ) :
    0 < ((step δ evaluate)^[n] r).2.2.1 ∧
      interval ((step δ evaluate)^[n] r) =
        (ApproximateBisection.step δ evaluate)^[n] (interval r) := by
  induction n with
  | zero => exact ⟨hr, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨step_den_pos δ evaluate _ ih.1, (step_interval δ evaluate _ ih.1).trans
      (congrArg (ApproximateBisection.step δ evaluate) ih.2)⟩

def bits (r : Registers) : ℕ :=
  max (max r.1.natAbs.bits.length r.2.1.natAbs.bits.length) r.2.2.1.bits.length

theorem code_length (r : Registers) : (code r).length =
    2 * r.1.natAbs.bits.length + 2 * r.2.1.natAbs.bits.length +
      2 * r.2.2.1.bits.length + 16 := by
  simp only [code, prodCode, intCode, intData, pairBits_length,
    Procedure.boolCode, List.length_singleton]
  omega

theorem bits_le_code (r : Registers) : bits r ≤ (code r).length := by
  rw [code_length]
  unfold bits
  omega

theorem code_le_bits (r : Registers) : (code r).length ≤ 6 * bits r + 16 := by
  rw [code_length]
  unfold bits
  omega

private theorem add_bits_le_max (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ max a.natAbs.bits.length b.natAbs.bits.length + 1 := by
  have hab : (a + b).natAbs ≤ 2 * max a.natAbs b.natAbs :=
    (Int.natAbs_add_le a b).trans (by omega)
  have h := (bits_length_mono hab).trans (double_bits_length (max a.natAbs b.natAbs))
  by_cases hm : a.natAbs ≤ b.natAbs
  · rw [max_eq_right hm] at h
    exact h.trans (Nat.add_le_add_right (le_max_right _ _) _)
  · rw [max_eq_left (le_of_not_ge hm)] at h
    exact h.trans (Nat.add_le_add_right (le_max_left _ _) _)

private theorem double_int_bits (a : ℤ) :
    (2 * a).natAbs.bits.length ≤ a.natAbs.bits.length + 1 := by
  rw [Int.natAbs_mul]
  exact double_bits_length a.natAbs

theorem step_bits (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) :
    bits (step δ evaluate r) ≤ bits r + 1 := by
  have ha := add_bits_le_max r.1 r.2.1
  have hl := double_int_bits r.1
  have hh := double_int_bits r.2.1
  have hd := double_bits_length r.2.2.1
  unfold step
  split_ifs <;> dsimp only [bits] <;> omega

theorem iterate_bits (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers) (n : ℕ) :
    bits ((step δ evaluate)^[n] r) ≤ bits r + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (step_bits δ evaluate _).trans (by omega)

/-- The actual unreduced register execution satisfies the analytic residual
bound; all evaluation calls remain inside the initial rational interval. -/
theorem residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (middle ((step δ evaluate)^[n] (initial a b)))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  obtain ⟨hp, hi⟩ := iterate_interval δ evaluate (initial a b) (initial_den_pos a b) n
  rw [middle_eq _ hp, hi, initial_interval]
  exact ApproximateBisection.run_residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionRegisters

end OAI
