import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalExponential
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.AmplificationProgram
import OAI.Computability.QuantumFactoring.BitStackRationals

namespace OAI

/-! A shared-denominator Taylor recurrence for arbitrary rational inputs.
The numerator may be signed. Register size grows polynomially in the
iteration count and the encoded numerator and denominator lengths. -/

namespace ContinuumCoulomb.RationalTaylorRegisters
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

abbrev State := ℤ × (ℕ × (ℕ × (ℤ × (ℕ × ℤ))))

def code : State → List Bool := prodCode intCode
  (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))

def step (s : State) : State :=
  let factor := (s.2.2.1 + 1) * s.2.1
  (s.1, s.2.1, s.2.2.1 + 1, (factor : ℤ) * (s.2.2.2.1 + s.2.2.2.2.2),
    factor * s.2.2.2.2.1, s.1 * s.2.2.2.2.2)

def initial (q : ℚ) : State := (q.num, q.den, 0, 0, 1, 1)

theorem iterate_initial (q : ℚ) (n : ℕ) :
    ((step^[n]) (initial q)).1 = q.num ∧
    ((step^[n]) (initial q)).2.1 = q.den ∧
    ((step^[n]) (initial q)).2.2.1 = n ∧
    (((step^[n]) (initial q)).2.2.2.1 : ℚ) =
      (n.factorial * q.den ^ n : ℕ) * RationalExponential.taylorSum q n ∧
    ((step^[n]) (initial q)).2.2.2.2.1 = n.factorial * q.den ^ n ∧
    ((step^[n]) (initial q)).2.2.2.2.2 = q.num ^ n := by
  induction n with
  | zero => simp [initial, RationalExponential.taylorSum]
  | succ n ih =>
    rcases ih with ⟨ha, hb, hj, hA, hF, hP⟩
    rw [Function.iterate_succ_apply']
    refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
    · change ((step^[n]) (initial q)).2.2.1 + 1 = n + 1
      rw [hj]
    · change (((((((step^[n]) (initial q)).2.2.1 + 1) *
        ((step^[n]) (initial q)).2.1 : ℕ) : ℤ) *
        (((step^[n]) (initial q)).2.2.2.1 +
          ((step^[n]) (initial q)).2.2.2.2.2) : ℤ) : ℚ) = _
      push_cast
      rw [hj, hb, hA, hP]
      have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have hnum : (q.num : ℚ) = q * q.den := by
        calc
          (q.num : ℚ) = ((q.num : ℚ) / q.den) * q.den := by field_simp
          _ = q * q.den := by rw [Rat.num_div_den]
      simp only [Nat.cast_mul, Nat.cast_pow, RationalExponential.taylorSum,
        Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_add, Nat.cast_one,
        hnum, mul_pow, Int.cast_pow, pow_succ]
      have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · change (((step^[n]) (initial q)).2.2.1 + 1) *
        ((step^[n]) (initial q)).2.1 * ((step^[n]) (initial q)).2.2.2.2.1 = _
      rw [hj, hb, hF, Nat.factorial_succ, pow_succ]
      ring
    · change ((step^[n]) (initial q)).1 * ((step^[n]) (initial q)).2.2.2.2.2 = _
      rw [ha, hP, pow_succ, mul_comm]

def result (s : State) : ℚ := mkRat s.2.2.2.1 s.2.2.2.2.1

theorem result_correct (q : ℚ) (n : ℕ) :
    result ((step^[n]) (initial q)) = RationalExponential.taylorSum q n := by
  obtain ⟨_, _, _, hA, hF, _⟩ := iterate_initial q n
  have hpos : 0 < q.den := q.pos
  have hden : (n.factorial * q.den ^ n : ℚ) ≠ 0 := by positivity
  unfold result
  rw [Rat.mkRat_eq_div, hA, hF]
  push_cast
  field_simp

def measure (s : State) : ℕ := s.1.natAbs.bits.length + s.2.1.bits.length +
  s.2.2.1.bits.length + max s.2.2.2.1.natAbs.bits.length s.2.2.2.2.2.natAbs.bits.length +
    s.2.2.2.2.1.bits.length

theorem code_length (s : State) : (code s).length =
    2 * s.1.natAbs.bits.length + 2 * s.2.1.bits.length + 2 * s.2.2.1.bits.length +
      2 * s.2.2.2.1.natAbs.bits.length + 2 * s.2.2.2.2.1.bits.length +
        s.2.2.2.2.2.natAbs.bits.length + 20 := by
  simp only [code, prodCode, intCode, intData, pairBits_length,
    Procedure.boolCode, List.length_singleton]
  omega

theorem measure_le_code (s : State) : measure s ≤ (code s).length := by
  rw [code_length]
  unfold measure
  omega

theorem code_le_measure (s : State) : (code s).length ≤ 3 * measure s + 20 := by
  rw [code_length]
  unfold measure
  omega

private theorem int_add_bits (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ max a.natAbs.bits.length b.natAbs.bits.length + 1 :=
  (bits_length_mono (Int.natAbs_add_le a b)).trans (AmplificationProgram.bits_add_max _ _)

theorem step_measure (s : State) : measure (step s) ≤
    measure s + s.1.natAbs.bits.length + 2 * s.2.1.bits.length + 2 * s.2.2.1.bits.length + 4 := by
  have hj := AmplificationProgram.bits_succ s.2.2.1
  have hf := bits_length_mul (s.2.2.1 + 1) s.2.1
  have hA := bits_length_mul ((s.2.2.1 + 1) * s.2.1)
    (s.2.2.2.1 + s.2.2.2.2.2).natAbs
  have ha := int_add_bits s.2.2.2.1 s.2.2.2.2.2
  have hF := bits_length_mul ((s.2.2.1 + 1) * s.2.1) s.2.2.2.2.1
  have hP := bits_length_mul s.1.natAbs s.2.2.2.2.2.natAbs
  have hm : max
      (((((s.2.2.1 + 1) * s.2.1 : ℕ) : ℤ) *
        (s.2.2.2.1 + s.2.2.2.2.2)).natAbs.bits.length)
      ((s.1 * s.2.2.2.2.2).natAbs.bits.length) ≤
      max s.2.2.2.1.natAbs.bits.length s.2.2.2.2.2.natAbs.bits.length +
        s.1.natAbs.bits.length + s.2.1.bits.length + s.2.2.1.bits.length + 2 := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    apply max_le <;> omega
  dsimp only [measure, step]
  omega

theorem iterate_parameters (s : State) (n : ℕ) :
    ((step^[n]) s).1 = s.1 ∧ ((step^[n]) s).2.1 = s.2.1 ∧
      ((step^[n]) s).2.2.1.bits.length ≤ s.2.2.1.bits.length + n := by
  induction n with
  | zero => exact ⟨rfl, rfl, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, ih.2.1, ?_⟩
    exact (AmplificationProgram.bits_succ _).trans (by omega)

theorem iterate_measure (s : State) (n : ℕ) :
    measure ((step^[n]) s) ≤ measure s + n * (5 * measure s + 2 * n + 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hstep := step_measure ((step^[n]) s)
    obtain ⟨ha, hb, hj⟩ := iterate_parameters s n
    rw [ha, hb] at hstep
    have h1 : s.1.natAbs.bits.length ≤ measure s := by unfold measure; omega
    have h2 : s.2.1.bits.length ≤ measure s := by unfold measure; omega
    have h3 : s.2.2.1.bits.length ≤ measure s := by unfold measure; omega
    nlinarith

theorem iterate_code_bound (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
    (code ((step^[i]) s)).length ≤
      (64 * (Polynomial.X + 1) ^ 2 + 100 : Polynomial ℕ).eval (n + (code s).length) := by
  have hc := code_le_measure ((step^[i]) s)
  have hm := iterate_measure s i
  have hs := measure_le_code s
  have hp := Nat.pow_le_pow_left hi 2
  have hmul := Nat.mul_le_mul hi hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end ContinuumCoulomb.RationalTaylorRegisters

end OAI
