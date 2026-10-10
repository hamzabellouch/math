import OAI.Computability.MatchingCount.BinarySolve

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def xor (a b : Bool) : Bool := if a then !b else b
def digit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (c && (a || b))

lemma fullAdder (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (digit a b c).toNat + 2 * (carry a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp only [List.cons_append, value, List.length_cons, pow_succ, ih]; ring

lemma value_head_tail (xs : List Bool) :
    value xs = (xs.headD false).toNat + 2 * value xs.tail := by
  cases xs <;> rfl

abbrev State := (List Bool × List Bool) × (Bool × List Bool)

def step (z : State × Bool) : State :=
  ((z.1.1.1.tail, z.1.1.2.tail),
    (carry (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1,
     z.1.2.2 ++ [digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1]))

def initial (z : List Bool × List Bool) : State := (z, (false, []))
def finish (s : State) : List Bool := s.2.2 ++ if s.2.1 then [true] else []

def run (l : List Bool) (s : State) : State := l.foldl (fun s b => step (s,b)) s

def add (z : List Bool × List Bool) : List Bool :=
  finish (run (z.1 ++ z.2) (initial z))

def potential (s : State) : ℕ :=
  value s.2.2 + 2 ^ s.2.2.length * (value s.1.1 + value s.1.2 + s.2.1.toNat)

lemma potential_step (s : State) (b : Bool) : potential (step (s,b)) = potential s := by
  rcases s with ⟨⟨xs,ys⟩,c,os⟩
  have h := fullAdder (xs.headD false) (ys.headD false) c
  have hx := value_head_tail xs
  have hy := value_head_tail ys
  simp only [potential, step, value_append, List.length_append, List.length_singleton,
    value, mul_zero, add_zero, pow_succ]
  rw [hx, hy]
  calc
    _ = value os + 2 ^ os.length *
        ((xs.headD false).toNat + (ys.headD false).toNat + c.toNat +
          2 * (value xs.tail + value ys.tail)) := by
      rw [h]
      ring
    _ = _ := by ring

lemma potential_run (l : List Bool) (s : State) : potential (run l s) = potential s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    change potential (run l (step (s,b))) = potential s
    rw [ih, potential_step]

lemma run_inputs (l : List Bool) (s : State) :
    (run l s).1 = (s.1.1.drop l.length, s.1.2.drop l.length) := by
  induction l generalizing s with
  | nil => simp [run]
  | cons b l ih =>
    change (run l (step (s,b))).1 = _
    rw [ih]
    simp only [step, List.length_cons]
    congr 1 <;> simp [List.drop_tail]

lemma run_length (l : List Bool) (s : State) :
    (run l s).2.2.length = s.2.2.length + l.length := by
  induction l generalizing s with
  | nil => simp [run]
  | cons b l ih =>
    change (run l (step (s,b))).2.2.length = _
    rw [ih]
    simp [step, Nat.add_comm, Nat.add_left_comm]

lemma value_finish (s : State) (h : s.1 = ([], [])) : value (finish s) = potential s := by
  rcases s with ⟨⟨xs,ys⟩,c,os⟩
  cases h
  cases c <;> simp [finish, potential, value_append, value]

theorem value_add (z : List Bool × List Bool) : value (add z) = value z.1 + value z.2 := by
  have hi : (run (z.1 ++ z.2) (initial z)).1 = ([], []) := by
    rw [run_inputs]
    simp only [initial, List.length_append]
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  rw [add, value_finish _ hi, potential_run]
  simp [potential, initial, value]

theorem length_add (z : List Bool × List Bool) :
    (add z).length ≤ z.1.length + z.2.length + 1 := by
  have h := run_length (z.1 ++ z.2) (initial z)
  simp only [initial, List.length_nil, zero_add, List.length_append] at h
  unfold add finish
  split <;> simp_all [initial]

lemma value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b <;> simp [value, ih, Nat.bit, Nat.add_comm]

theorem value_add_bits (m n : ℕ) : value (add (m.bits,n.bits)) = m+n := by
  rw [value_add, value_bits, value_bits]

end LoopMatching.BitAdd

end OAI
