import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableAmplification
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.BinaryEncoding
import OAI.Computability.QuantumFactoring.BitStackUnary
import OAI.Computability.QuantumFactoring.BitStackDivision

namespace OAI

/-! A binary stack-machine implementation of the exact rational Taylor
amplification used for the binary nuclear charges. The input parameter D is
unary; the large output and every arithmetic register are binary. -/

namespace ContinuumCoulomb.AmplificationProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

abbrev State := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

def stateCode : State → List Bool := prodCode Nat.bits
  (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))

def step (s : State) : State :=
  (s.1, s.2.1 + 1, (s.2.1 + 1) * (s.2.2.1 + s.2.2.2.2),
    (s.2.1 + 1) * s.2.2.2.1, s.1 * s.2.2.2.2)

def start (D : ℕ) : State := (D, 0, 0, 1, 1)

def partialTaylor (D n : ℕ) : ℚ := ∑ j ∈ Finset.range n, (D : ℚ) ^ j / (j.factorial : ℚ)

/-- Scaled numerator, factorial denominator and power are maintained by
literal natural-number additions and multiplications. -/
theorem iterate_start (D n : ℕ) :
    ((step^[n]) (start D)).1 = D ∧
    ((step^[n]) (start D)).2.1 = n ∧
    (((step^[n]) (start D)).2.2.1 : ℚ) = (n.factorial : ℚ) * partialTaylor D n ∧
    ((step^[n]) (start D)).2.2.2.1 = n.factorial ∧
    ((step^[n]) (start D)).2.2.2.2 = D ^ n := by
  induction n with
  | zero => simp [start, partialTaylor]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with ⟨hD, hk, hA, hF, hP⟩
    refine ⟨hD, ?_, ?_, ?_, ?_⟩
    · change ((step^[n]) (start D)).2.1 + 1 = n + 1
      rw [hk]
    · change (((((step^[n]) (start D)).2.1 + 1) *
        (((step^[n]) (start D)).2.2.1 + ((step^[n]) (start D)).2.2.2.2) : ℕ) : ℚ) = _
      rw [hk, hP]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hA, partialTaylor,
        Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow]
      have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · change (((step^[n]) (start D)).2.1 + 1) * ((step^[n]) (start D)).2.2.2.1 =
        (n + 1).factorial
      rw [hk, hF, Nat.factorial_succ]
    · change ((step^[n]) (start D)).1 * ((step^[n]) (start D)).2.2.2.2 = D ^ (n + 1)
      rw [hD, hP, pow_succ, Nat.mul_comm]

/-- Natural ceiling of a nonnegative rational quotient is computed with
addition, subtraction by one, and ordinary natural division. -/
theorem ceil_nat_ratio (A F : ℕ) (hF : 0 < F) :
    Nat.ceil ((A : ℚ) / F) = (A + F - 1) / F := by
  change Nat.ceil ((A : ℚ) / F) = A ⌈/⌉ F
  have hFq : (0 : ℚ) < F := by exact_mod_cast hF
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hFq).mpr
    have hmul : A ≤ (A ⌈/⌉ F) * F := by
      exact Nat.mul_comm F (A ⌈/⌉ F) ▸
        ((ceilDiv_le_iff_le_mul hF).mp (le_refl (A ⌈/⌉ F)))
    exact_mod_cast hmul
  · apply (ceilDiv_le_iff_le_mul hF).mpr
    have h := (div_le_iff₀ hFq).mp (Nat.le_ceil ((A : ℚ) / F))
    have hmul : A ≤ Nat.ceil ((A : ℚ) / F) * F := by exact_mod_cast h
    simpa only [Nat.mul_comm] using hmul

def result (s : State) : ℕ := (s.2.2.1 + s.2.2.2.1 - 1) / s.2.2.2.1

theorem result_correct (D : ℕ) :
    result ((step^[amplificationOrder D]) (start D)) = taylorAmplification D := by
  let n := amplificationOrder D
  rcases iterate_start D n with ⟨_, _, hA, hF, _⟩
  have hFq : (n.factorial : ℚ) ≠ 0 := by positivity
  have hratio : (((step^[n]) (start D)).2.2.1 : ℚ) / ((step^[n]) (start D)).2.2.2.1 =
      amplificationTaylor D := by
    rw [hF, hA, mul_div_cancel_left₀ _ hFq]
    rfl
  change result ((step^[n]) (start D)) = Nat.ceil (amplificationTaylor D)
  rw [← hratio]
  exact (ceil_nat_ratio _ _ (by rw [hF]; exact Nat.factorial_pos n)).symm

/-- Addition costs at most one more bit than the larger input. -/
theorem bits_add_max (a b : ℕ) :
    (a + b).bits.length ≤ max a.bits.length b.bits.length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hap : 2 ^ a.size ≤ 2 ^ max a.size b.size := by
    apply Nat.pow_le_pow_right (by decide)
    exact le_max_left a.size b.size
  have hbp : 2 ^ b.size ≤ 2 ^ max a.size b.size := by
    apply Nat.pow_le_pow_right (by decide)
    exact le_max_right a.size b.size
  omega

theorem bits_succ (a : ℕ) : (a + 1).bits.length ≤ a.bits.length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hp : 0 < 2 ^ a.size := by positivity
  omega

def measure (s : State) : ℕ := s.1.bits.length + s.2.1.bits.length +
  max s.2.2.1.bits.length s.2.2.2.2.bits.length + s.2.2.2.1.bits.length

theorem stateCode_length (s : State) : (stateCode s).length =
    2 * s.1.bits.length + 2 * s.2.1.bits.length + 2 * s.2.2.1.bits.length +
      2 * s.2.2.2.1.bits.length + s.2.2.2.2.bits.length + 4 := by
  simp only [stateCode, prodCode, pairBits_length]
  omega

theorem measure_le_code (s : State) : measure s ≤ (stateCode s).length := by
  rw [stateCode_length]
  unfold measure
  have hm : max s.2.2.1.bits.length s.2.2.2.2.bits.length ≤
      s.2.2.1.bits.length + s.2.2.2.2.bits.length := by omega
  omega

theorem code_le_measure (s : State) : (stateCode s).length ≤ 3 * measure s + 4 := by
  rw [stateCode_length]
  unfold measure
  have ha := le_max_left s.2.2.1.bits.length s.2.2.2.2.bits.length
  have hp := le_max_right s.2.2.1.bits.length s.2.2.2.2.bits.length
  omega

theorem step_measure (s : State) :
    measure (step s) ≤ measure s + s.1.bits.length + 2 * s.2.1.bits.length + 4 := by
  have hk := bits_succ s.2.1
  have ha := bits_length_mul (s.2.1 + 1) (s.2.2.1 + s.2.2.2.2)
  have has := bits_add_max s.2.2.1 s.2.2.2.2
  have hf := bits_length_mul (s.2.1 + 1) s.2.2.2.1
  have hp := bits_length_mul s.1 s.2.2.2.2
  have hp0 := le_max_right s.2.2.1.bits.length s.2.2.2.2.bits.length
  dsimp only [measure, step]
  have hm : max ((s.2.1 + 1) * (s.2.2.1 + s.2.2.2.2)).bits.length
      (s.1 * s.2.2.2.2).bits.length ≤
      max s.2.2.1.bits.length s.2.2.2.2.bits.length + s.1.bits.length + s.2.1.bits.length + 2 := by
    apply max_le <;> omega
  omega

theorem iterate_D (s : State) (i : ℕ) : ((step^[i]) s).1 = s.1 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply']; exact ih

theorem iterate_index_bits (s : State) (i : ℕ) :
    ((step^[i]) s).2.1.bits.length ≤ s.2.1.bits.length + i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change (((step^[i]) s).2.1 + 1).bits.length ≤ _
    have h := bits_succ ((step^[i]) s).2.1
    omega

theorem iterate_measure (s : State) (i : ℕ) :
    measure ((step^[i]) s) ≤ measure s + i * (3 * measure s + i + 4) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hstep := step_measure ((step^[i]) s)
    rw [iterate_D] at hstep
    have hk := iterate_index_bits s i
    have hD : s.1.bits.length ≤ measure s := by unfold measure; omega
    have hk0 : s.2.1.bits.length ≤ measure s := by unfold measure; omega
    nlinarith

/-- The entire arithmetic state stays polynomial in iteration count and
initial binary input size, including arbitrary initial register contents. -/
theorem iterate_code_bound (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
    (stateCode ((step^[i]) s)).length ≤
      (16 * (Polynomial.X + 1) ^ 2 + 16 : Polynomial ℕ).eval (n + (stateCode s).length) := by
  have hc := code_le_measure ((step^[i]) s)
  have hm := iterate_measure s i
  have hs := measure_le_code s
  have hi2 := Nat.pow_le_pow_left hi 2
  have him := Nat.mul_le_mul hi hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

noncomputable def stepProgram : Procedure stateCode stateCode step := by
  let d := Procedure.first Nat.bits (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))
  let t := Procedure.second Nat.bits (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))
  let k := (Procedure.first Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits))).comp t
  let u := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits))).comp t
  let a := (Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)).comp u
  let v := (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)).comp u
  let f := (Procedure.first Nat.bits Nat.bits).comp v
  let p := (Procedure.second Nat.bits Nat.bits).comp v
  let next := Procedure.successor.comp k
  let numerator := Procedure.binaryMul.comp (next.pair (Procedure.binaryAdd.comp (a.pair p)))
  let factorial := Procedure.binaryMul.comp (next.pair f)
  let power := Procedure.binaryMul.comp (d.pair p)
  exact (d.pair (next.pair (numerator.pair (factorial.pair power)))).congrFun (by intro s; rfl)

noncomputable def repeatProgram : Procedure (prodCode unaryCode stateCode) stateCode
    (fun x => (step^[x.1]) x.2) :=
  stepProgram.iterate (16 * (Polynomial.X + 1) ^ 2 + 16) iterate_code_bound

noncomputable def orderProgram : Procedure unaryCode unaryCode amplificationOrder := by
  let d := Procedure.identity unaryCode
  let square := Procedure.unaryMul.comp (d.pair d)
  let four := Procedure.constant unaryCode unaryCode 4
  let fourSquare := Procedure.unaryMul.comp (four.pair square)
  exact (Procedure.unaryAdd.comp (fourSquare.pair four)).congrFun (by
    intro D
    change 4 * (D * D) + 4 = amplificationOrder D
    unfold amplificationOrder
    ring)

noncomputable def startProgram : Procedure unaryCode stateCode start := by
  let d := Procedure.unaryToBits
  let zero := Procedure.constant unaryCode Nat.bits 0
  let one := Procedure.constant unaryCode Nat.bits 1
  exact (d.pair (zero.pair (zero.pair (one.pair one)))).congrFun (by intro D; rfl)

noncomputable def resultProgram : Procedure stateCode Nat.bits result := by
  let t := Procedure.second Nat.bits (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))
  let u := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits))).comp t
  let a := (Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)).comp u
  let v := (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)).comp u
  let f := (Procedure.first Nat.bits Nat.bits).comp v
  let pred := Procedure.binarySub.comp ((Procedure.binaryAdd.comp (a.pair f)).pair
    (Procedure.constant stateCode Nat.bits 1))
  exact (Procedure.binaryDiv.comp (pred.pair f)).congrFun (by intro s; rfl)

/-- Every step is compiled from actual binary add/multiply/divide routines;
the repetition count is polynomial in the unary input size. -/
noncomputable def rawProgram : Procedure unaryCode Nat.bits taylorAmplification :=
  (resultProgram.comp (repeatProgram.comp (orderProgram.pair startProgram))).congrFun result_correct

theorem encodeUnary_replicate (D : ℕ) :
    BinaryEncoding.encodeUnary D = List.replicate D true ++ [false] := by
  induction D with
  | zero => rfl
  | succ D ih => simp only [BinaryEncoding.encodeUnary, List.replicate_succ, List.cons_append, ih]

theorem encodeDigits_quote (bits : List Bool) : BinaryEncoding.encodeDigits bits = quoteBits bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [BinaryEncoding.encodeDigits, quoteBits_cons, ih]

/-- Strip the false unary terminator with two actual reversals and one pop. -/
noncomputable def inputProgram : Procedure BinaryEncoding.unary.encode unaryCode id := by
  let strip := (Procedure.reverse.comp (Procedure.tail.comp Procedure.reverse)).precompose
    BinaryEncoding.unary.encode
  exact strip.result (by
    intro D
    change ((BinaryEncoding.encodeUnary D).reverse.tail).reverse = List.replicate D true
    rw [encodeUnary_replicate]
    simp)

/-- Exact amplification with explicit prefix encodings and a finite polynomial-time
machine. -/
noncomputable def certificate :
    Turing.TM2ComputableInPolyTime BinaryEncoding.unary.encode BinaryEncoding.natural.encode
      taylorAmplification := by
  let quoted := (Procedure.quote Nat.bits).comp rawProgram
  let encoded : Procedure unaryCode BinaryEncoding.natural.encode taylorAmplification :=
    quoted.result (by intro D; exact (encodeDigits_quote (taylorAmplification D).bits).symm)
  exact (encoded.comp inputProgram).toTM2

end ContinuumCoulomb.AmplificationProgram

end OAI
