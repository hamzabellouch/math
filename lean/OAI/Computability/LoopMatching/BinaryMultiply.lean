import OAI.Computability.LoopMatching.BitNormalize

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.SmallBinaryMultiply
open BinaryMatching.StackCode Polynomial

abbrev State := List Bool × List Bool

def step (s : State) : State := (s.1, BitNormalize.add (s.1,s.2))
def initial (z : ℕ × List Bool) : State := (z.2, [])
def mul (z : ℕ × List Bool) : List Bool := (step^[z.1] (initial z)).2

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

lemma orbit_first (z : ℕ × List Bool) (k : ℕ) :
    (step^[k] (initial z)).1 = z.2 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', step] using ih

lemma orbit_value (z : ℕ × List Bool) (k : ℕ) :
    BitAdd.value (step^[k] (initial z)).2 = k * BitAdd.value z.2 := by
  induction k with
  | zero => simp [initial, BitAdd.value]
  | succ k ih =>
    simp only [Function.iterate_succ_apply', step, BitNormalize.value_add,
      orbit_first, ih]
    ring

lemma orbit_length (z : ℕ × List Bool) (k : ℕ) :
    (step^[k] (initial z)).2.length ≤ z.2.length + k := by
  induction k with
  | zero => simp [initial]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (BitNormalize.add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)).length ≤ z.2.length + (k+1)
    have h := BitNormalize.length_add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)
    change (BitNormalize.add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)).length ≤
        max (step^[k] (initial z)).1.length (step^[k] (initial z)).2.length + 1 at h
    rw [orbit_first] at h ⊢
    have hm : max z.2.length (step^[k] (initial z)).2.length ≤ z.2.length+k :=
      max_le (by omega) ih
    exact h.trans (Nat.add_le_add_right hm 1)

lemma orbit_code_length (z : ℕ × List Bool) (k : ℕ) :
    (encode (step^[k] (initial z))).length ≤ 9*z.2.length+3*k+1 := by
  rw [code_pair_length, BitAdd.boolList_code_length,
    BitAdd.boolList_code_length, orbit_first]
  have h := orbit_length z k
  omega

@[fun_prop] theorem orbit_poly :
    Poly (fun z : ℕ × List Bool => step^[z.1] (initial z)) := by
  apply Poly.iterateFrom step step_poly Prod.fst initial (by fun_prop)
    initial_poly (10*(X+1))
  intro z k hk
  have h := orbit_code_length z k
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have he : (encode (z.1,initial z)).length = 2*z.1+6*z.2.length+2 := by
    simp only [initial, code_pair_length, code_nat_length,
      BitAdd.boolList_code_length, List.length_nil]
    omega
  change (encode (step^[k] (initial z))).length ≤
    10*((encode (z.1,initial z)).length+1)
  rw [he]
  omega

@[fun_prop] theorem mul_poly : Poly mul := by
  unfold mul
  fun_prop

theorem value_mul (z : ℕ × List Bool) :
    BitAdd.value (mul z) = z.1 * BitAdd.value z.2 := orbit_value z z.1

theorem length_mul (z : ℕ × List Bool) :
    (mul z).length ≤ z.2.length + z.1 := orbit_length z z.1

def horner (z : (ℕ × List Bool) × List Bool) : List Bool :=
  BitNormalize.add (mul z.1,z.2)

@[fun_prop] theorem horner_poly : Poly horner := by
  unfold horner
  fun_prop

theorem value_horner (z : (ℕ × List Bool) × List Bool) :
    BitAdd.value (horner z) = z.1.1 * BitAdd.value z.1.2 + BitAdd.value z.2 := by
  simp only [horner, BitNormalize.value_add, value_mul]

theorem length_horner (z : (ℕ × List Bool) × List Bool) :
    (horner z).length ≤ max z.1.2.length z.2.length + z.1.1 + 1 := by
  have ha := BitNormalize.length_add (mul z.1,z.2)
  change (BitNormalize.add (mul z.1,z.2)).length ≤
    max (mul z.1).length z.2.length + 1 at ha
  have hm := length_mul z.1
  have hx := le_max_left z.1.2.length z.2.length
  have hy := le_max_right z.1.2.length z.2.length
  have hb : max (mul z.1).length z.2.length ≤
      max z.1.2.length z.2.length + z.1.1 := max_le (by omega) (by omega)
  exact ha.trans (Nat.add_le_add_right hb 1)

end LoopMatching.SmallBinaryMultiply

end OAI
