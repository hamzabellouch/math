import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EncodingPrograms
import OAI.Computability.QuantumFactoring.BitStackPowers
import OAI.Computability.QuantumFactoring.BinaryRoots

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

abbrev State := ℕ × (ℕ × ℕ)

def code : State → List Bool := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

def step (s : State) : State :=
  let half := s.2.1 / 2
  let candidate := s.2.2 + half
  (s.1, half, if candidate * candidate ≤ s.1 then candidate else s.2.2)

def root (m : ℕ) : ℕ :=
  ExactQuantumFactoring.Primality.boundedRoot m 2 m.bits.length

theorem iterate_power (m k g : ℕ) :
    (step^[k]) (m, 2 ^ k, g) =
      (m, 1, ExactQuantumFactoring.Primality.rootSearch m 2 k g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by simp [pow_succ]
    simp only [step, hhalf, ← pow_two, ExactQuantumFactoring.Primality.rootSearch]
    exact ih _

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

theorem root_le_sqrt (m : ℕ) : (root m : ℝ) ≤ Real.sqrt m := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  exact_mod_cast (root_spec m).1

theorem sqrt_lt_root_add_one (m : ℕ) : Real.sqrt m < (root m : ℝ) + 1 := by
  apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
  exact_mod_cast (root_spec m).2

def measure (s : State) : ℕ := s.1.bits.length + s.2.1.bits.length + s.2.2.bits.length

theorem code_length (s : State) :
    (code s).length = 2 * s.1.bits.length + 2 * s.2.1.bits.length + s.2.2.bits.length + 2 := by
  simp only [code, prodCode, pairBits_length]
  omega

theorem measure_le_code (s : State) : measure s ≤ (code s).length := by
  rw [code_length]
  unfold measure
  omega

theorem code_le_measure (s : State) : (code s).length ≤ 2 * measure s + 2 := by
  rw [code_length]
  unfold measure
  omega

theorem step_measure (s : State) : measure (step s) ≤ measure s + s.2.1.bits.length + 1 := by
  have hhalf : (s.2.1 / 2).bits.length ≤ s.2.1.bits.length :=
    bits_length_mono (Nat.div_le_self _ _)
  have hc := bits_length_add s.2.2 (s.2.1 / 2)
  dsimp only [measure, step]
  split_ifs <;> omega

theorem iterate_half_bits (s : State) (i : ℕ) :
    ((step^[i]) s).2.1.bits.length ≤ s.2.1.bits.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (bits_length_mono (Nat.div_le_self _ _)).trans ih

theorem iterate_measure (s : State) (i : ℕ) :
    measure ((step^[i]) s) ≤ measure s + i * (measure s + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have h := step_measure ((step^[i]) s)
    have hp := iterate_half_bits s i
    have hp0 : s.2.1.bits.length ≤ measure s := by unfold measure; omega
    nlinarith

theorem iterate_code_bound (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
    (code ((step^[i]) s)).length ≤
      (8 * (Polynomial.X + 1) ^ 2 + 8 : Polynomial ℕ).eval (n + (code s).length) := by
  have hc := code_le_measure ((step^[i]) s)
  have hm := iterate_measure s i
  have hs := measure_le_code s
  have him := Nat.mul_le_mul hi hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

noncomputable def stepProgram : Procedure code code step := by
  let m := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let p := (Procedure.first Nat.bits Nat.bits).comp rest
  let g := (Procedure.second Nat.bits Nat.bits).comp rest
  let half := Procedure.binaryDiv.comp (p.pair (Procedure.constant code Nat.bits 2))
  let candidate := Procedure.binaryAdd.comp (g.pair half)
  let square := Procedure.binaryMul.comp (candidate.pair candidate)
  let test := Procedure.binaryLe.comp (square.pair m)
  let newGuess := Procedure.conditional test candidate g
  exact (m.pair (half.pair newGuess)).congrFun (by
    intro s
    simp only [step, Function.comp_apply, decide_eq_true_eq])

noncomputable def repeatProgram : Procedure (prodCode unaryCode code) code
    (fun x => (step^[x.1]) x.2) :=
  stepProgram.iterate (8 * (Polynomial.X + 1) ^ 2 + 8) iterate_code_bound

noncomputable def rawProgram : Procedure Nat.bits Nat.bits root := by
  let m := Procedure.identity Nat.bits
  let n := Procedure.length.precompose Nat.bits
  let power := Procedure.binaryPow.comp (n.pair (Procedure.constant Nat.bits Nat.bits 2))
  let state := m.pair (power.pair (Procedure.constant Nat.bits Nat.bits 0))
  let run := repeatProgram.comp (n.pair state)
  let guess := (Procedure.second Nat.bits Nat.bits).comp
    (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits))
  exact (guess.comp run).congrFun (by
    intro m
    change ((step^[m.bits.length]) (m, 2 ^ m.bits.length, 0)).2.2 = root m
    rw [iterate_power]
    rfl)

noncomputable def program : Procedure BinaryEncoding.natural.encode BinaryEncoding.natural.encode root :=
  EncodingPrograms.naturalOutput.comp (rawProgram.comp EncodingPrograms.naturalInput)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime BinaryEncoding.natural.encode BinaryEncoding.natural.encode root :=
  program.toTM2

end ContinuumCoulomb.SquareRootProgram

end OAI
