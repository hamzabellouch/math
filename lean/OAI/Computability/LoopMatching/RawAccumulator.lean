import OAI.Computability.LoopMatching.BinaryMultiply
import OAI.Computability.LoopMatching.InputMachine
import OAI.Computability.LoopMatching.Accumulator

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.RawAccumulator
open BinaryMatching.StackCode Polynomial

abbrev Data := InputMachine.Data
abbrev State := Data × (ℕ × (List Bool × List Bool))

def step (s : State) : State :=
  (s.1,(s.2.1+1,
    (SmallBinaryMultiply.horner ((s.2.1+1,s.2.2.1),InputMachine.call s.1 (s.2.1+1)),
     SmallBinaryMultiply.mul (s.2.1+1,s.2.2.2))))

def initial (z : Data) : State := (z,(0,(InputMachine.call z 0,[true])))
def rawAccumulator (z : Data) : List Bool × List Bool :=
  (step^[z.1] (initial z)).2.2

def term (z : Data) (j : ℕ) : ℕ := BitAdd.value (InputMachine.call z j)

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

lemma orbit_context (z : Data) (k : ℕ) : (step^[k] (initial z)).1 = z := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', step] using ih

lemma orbit_index (z : Data) (k : ℕ) : (step^[k] (initial z)).2.1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', step, ih]

lemma orbit_values (z : Data) (k : ℕ) :
    BitAdd.value (step^[k] (initial z)).2.2.1 = Accumulator.Q (term z) k ∧
    BitAdd.value (step^[k] (initial z)).2.2.2 = k.factorial := by
  induction k with
  | zero => simp [initial, Accumulator.Q, term, BitAdd.value]
  | succ k ih =>
    constructor <;> simp only [Function.iterate_succ_apply', step, orbit_context, orbit_index,
      SmallBinaryMultiply.value_horner, SmallBinaryMultiply.value_mul,
      ih.1, ih.2, Accumulator.Q_succ, Nat.factorial_succ, term]

lemma orbit_lengths (z : Data) (M k : ℕ) (hk : k ≤ z.1)
    (hcall : ∀ j ≤ z.1, (InputMachine.call z j).length ≤ M) :
    (step^[k] (initial z)).2.2.1.length ≤ M+k*(z.1+2) ∧
    (step^[k] (initial z)).2.2.2.length ≤ 1+k*(z.1+1) := by
  induction k with
  | zero =>
    constructor
    · simpa only [Function.iterate_zero_apply, initial, Nat.zero_mul,
        Nat.add_zero] using hcall 0 (by omega)
    · simp [initial]
  | succ k ih =>
    obtain ⟨hq,hd⟩ := ih (by omega)
    have hc := hcall (k+1) hk
    have hq' := SmallBinaryMultiply.length_horner
      ((k+1,(step^[k] (initial z)).2.2.1),InputMachine.call z (k+1))
    have hd' := SmallBinaryMultiply.length_mul (k+1,(step^[k] (initial z)).2.2.2)
    have hm : max (step^[k] (initial z)).2.2.1.length
        (InputMachine.call z (k+1)).length ≤ M+k*(z.1+2) :=
      max_le hq (by omega)
    simp only [Function.iterate_succ_apply', step, orbit_context, orbit_index]
    constructor <;> nlinarith

noncomputable def callBound : Polynomial ℕ :=
  (X + InputMachine.call_poly.routine.time).comp (3*X+1)

lemma call_length_bound (z : Data) (N j : ℕ)
    (hz : (encode z).length ≤ N) (hj : j ≤ N) :
    (InputMachine.call z j).length ≤ callBound.eval N := by
  have hin : (encode (z,j)).length ≤ 3*N+1 := by
    rw [code_pair_length, code_nat_length]
    change 2*(encode z).length+j+1 ≤ 3*N+1
    omega
  have ho := InputMachine.call_poly.routine.length_bound (z,j)
  change (encode (InputMachine.call z j)).length ≤ (encode (z,j)).length +
    InputMachine.call_poly.routine.time.eval (encode (z,j)).length at ho
  have hm := polynomial_eval_mono InputMachine.call_poly.routine.time hin
  change InputMachine.call_poly.routine.time.eval (encode (z,j)).length ≤
    InputMachine.call_poly.routine.time.eval (3*N+1) at hm
  rw [BitAdd.boolList_code_length] at ho
  simp only [callBound, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

lemma state_code_length (s : State) :
    (encode s).length = 2*(encode s.1).length + 2*s.2.1 +
      6*s.2.2.1.length + 3*s.2.2.2.length + 3 := by
  simp only [code_pair_length, code_nat_length, BitAdd.boolList_code_length]
  omega

noncomputable def orbitBound : Polynomial ℕ := 20*(callBound+(X+1)^2+1)

lemma orbit_bound (z : Data) (k : ℕ) (hk : k ≤ z.1) :
    (encode (step^[k] (initial z))).length ≤
      orbitBound.eval (encode (z.1,initial z)).length := by
  let N := (encode (z.1,initial z)).length
  have hz : (encode z).length ≤ N := by
    simp only [N, initial, code_pair_length, code_nat_length]
    omega
  have hn : z.1 ≤ N := by
    simp only [N, code_pair_length, code_nat_length]
    omega
  have hc : ∀ j ≤ z.1, (InputMachine.call z j).length ≤ callBound.eval N := by
    intro j hj
    exact call_length_bound z N j hz (hj.trans hn)
  obtain ⟨hq,hd⟩ := orbit_lengths z (callBound.eval N) k hk hc
  have hkN := hk.trans hn
  have hqmul : k*(z.1+2) ≤ N*(N+2) := Nat.mul_le_mul hkN (by omega)
  have hdmul : k*(z.1+1) ≤ N*(N+1) := Nat.mul_le_mul hkN (by omega)
  rw [state_code_length, orbit_context, orbit_index]
  change 2*(encode z).length + 2*k + 6*(step^[k] (initial z)).2.2.1.length +
    3*(step^[k] (initial z)).2.2.2.length + 3 ≤ orbitBound.eval N
  simp only [orbitBound, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

@[fun_prop] theorem orbit_poly : Poly (fun z : Data => step^[z.1] (initial z)) := by
  exact Poly.iterateFrom step step_poly Prod.fst initial (by fun_prop)
    initial_poly orbitBound orbit_bound

@[fun_prop] theorem rawAccumulator_poly : Poly rawAccumulator := by
  unfold rawAccumulator
  fun_prop

theorem rawAccumulator_values (z : Data) :
    BitAdd.value (rawAccumulator z).1 = Accumulator.Q (term z) z.1 ∧
    BitAdd.value (rawAccumulator z).2 = z.1.factorial := orbit_values z z.1

lemma term_repr (G : LoopMatching.Input) (j : ℕ) :
    term (InputMachine.repr G) j =
      BinaryMatching.Raw.InputData.sparseEstimate (expand G j) := by
  rw [term, InputMachine.call_repr, BitAdd.value_bits]

theorem rawAccumulator_repr (G : LoopMatching.Input) :
    BitAdd.value (rawAccumulator (InputMachine.repr G)).1 =
      Accumulator.Q (fun j => BinaryMatching.Raw.InputData.sparseEstimate (expand G j)) G.n ∧
    BitAdd.value (rawAccumulator (InputMachine.repr G)).2 = G.n.factorial := by
  have ht : term (InputMachine.repr G) =
      fun j => BinaryMatching.Raw.InputData.sparseEstimate (expand G j) :=
    funext (term_repr G)
  have hv := rawAccumulator_values (InputMachine.repr G)
  rw [ht] at hv
  exact hv

end LoopMatching.RawAccumulator

end OAI
