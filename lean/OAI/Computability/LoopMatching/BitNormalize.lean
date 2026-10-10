import OAI.Computability.LoopMatching.BitAddRoutine
import OAI.Computability.LoopMatching.BitLength

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitNormalize
open BinaryMatching.StackCode
open BitAdd (value)

def step (z : List Bool × Bool) : List Bool :=
  if z.2 then true :: z.1 else if z.1.isEmpty then [] else false :: z.1

def normalize (l : List Bool) : List Bool :=
  l.foldr (fun b acc => step (acc,b)) []

lemma normalize_cons (b : Bool) (l : List Bool) :
    normalize (b::l) = step (normalize l,b) := rfl

lemma step_length (l : List Bool) (b : Bool) :
    (step (l,b)).length ≤ l.length+1 := by
  cases b <;> cases l <;> simp [step]

theorem length_normalize (l : List Bool) : (normalize l).length ≤ l.length := by
  induction l with
  | nil => simp [normalize]
  | cons b l ih =>
    rw [normalize_cons]
    have h := step_length (normalize l) b
    simp only [List.length_cons]
    omega

lemma value_step (l : List Bool) (b : Bool) :
    value (step (l,b)) = b.toNat + 2*value l := by
  cases b <;> cases l <;> simp [step, value]

theorem value_normalize (l : List Bool) : value (normalize l) = value l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [normalize_cons, value_step, ih]; rfl

theorem normalize_eq_bits (l : List Bool) : normalize l = (value l).bits := by
  induction l with
  | nil => simp [normalize, value]
  | cons b l ih =>
    rw [normalize_cons, ih]
    by_cases hz : value l = 0
    · cases b <;> simp [step, value, hz]
    · have hb : value l = 0 → b = true := fun h => (hz h).elim
      have hn : (value l).bits ≠ [] := by
        intro h
        have hv := BitAdd.value_bits (value l)
        rw [h] at hv
        exact hz hv.symm
      have he : ((value l).bits).isEmpty = false := by
        cases h : (value l).bits with
        | nil => exact (hn h).elim
        | cons a as => rfl
      have hv : value (b::l) = Nat.bit b (value l) := by
        cases b <;> simp [value, Nat.bit]; omega
      rw [hv, Nat.bits_append_bit _ _ hb]
      cases b <;> simp [step, he]

theorem normalize_bits (n : ℕ) : normalize n.bits = n.bits := by
  rw [normalize_eq_bits, BitAdd.value_bits]

theorem normalize_idempotent (l : List Bool) : normalize (normalize l) = normalize l := by
  rw [normalize_eq_bits l, normalize_bits]

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

lemma step_growth (z : List Bool × Bool) :
    (encode (step z)).length ≤ (encode z.1).length + 1*(2*(encode z.2).length+1) := by
  rw [BitAdd.boolList_code_length, BitAdd.boolList_code_length]
  simp only [encode_bool, List.length_singleton]
  have h := step_length z.1 z.2
  change (step z).length ≤ z.1.length + 1 at h
  omega

@[fun_prop] theorem normalize_poly : Poly normalize := by
  have hf := Poly.listFoldAdd step step_poly 1 step_growth
  have hh := Poly.comp _ (fun l : List Bool => (l.reverse, ([] : List Bool))) hf (by fun_prop)
  exact hh.congr (fun l => by simp [normalize, List.foldl_reverse])

def add (z : List Bool × List Bool) : List Bool := normalize (BitAdd.add z)

@[fun_prop] theorem add_poly : Poly add := by unfold add; fun_prop

theorem add_eq_bits (z : List Bool × List Bool) :
    add z = (value z.1 + value z.2).bits := by
  rw [add, normalize_eq_bits, BitAdd.value_add]

theorem value_add (z : List Bool × List Bool) : value (add z) = value z.1 + value z.2 := by
  rw [add, value_normalize, BitAdd.value_add]

theorem add_bits (m n : ℕ) : add (m.bits,n.bits) = (m+n).bits := by
  rw [add_eq_bits, BitAdd.value_bits, BitAdd.value_bits]

theorem length_add (z : List Bool × List Bool) :
    (add z).length ≤ max z.1.length z.2.length + 1 := by
  rw [add_eq_bits]
  exact BitAdd.length_bits_value_add z.1 z.2

end LoopMatching.BitNormalize

end OAI
