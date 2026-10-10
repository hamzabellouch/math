import Mathlib

namespace OAI

namespace Fifths

/- pair on binary stacks. First component length `a.size`
costs exactly 2a.size+1 extra cells; does *not* double the second
component. Used also for encoding continuations. -/
namespace Bin

def val : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (val l)

theorem val_bits (n : ℕ) : val n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [val]
  | bit b n h ih => simp [Nat.bits_append_bit _ _ h, val, ih]

def esc (b : Bool) := [false, b]
def frame (l r : List Bool) : List Bool := l.flatMap esc ++ true :: r

@[simp] theorem frame_nil (r : List Bool) : frame [] r = true :: r := rfl
@[simp] theorem frame_cons (b : Bool) (l r : List Bool) :
    frame (b :: l) r = false :: b :: frame l r := by simp [frame,esc]

def pair (u v : ℕ) : ℕ := val (frame u.bits v.bits)

theorem frameLength (l r) : (frame l r).length = 2*l.length + 1 + r.length := by
  induction l with
  | nil => simp; omega
  | cons b l ih => simp [ih]; omega

private theorem bitTrue (n : ℕ) : Nat.bit true n ≠ 0 := by
  simp [Nat.bit]

theorem frameBits (l) (n : ℕ) :
    val (frame l n.bits) ≠ 0 ∧ (val (frame l n.bits)).bits = frame l n.bits := by
  induction l with
  | nil =>
    rw [frame_nil, val, val_bits]
    exact ⟨bitTrue _, Nat.bits_append_bit n true (fun _ => rfl)⟩
  | cons b l ih =>
    obtain ⟨a,c⟩ := ih
    rw [frame_cons,val,val]
    have h := Nat.bit_ne_zero b a
    refine ⟨Nat.bit_ne_zero _ h, ?_⟩
    rw [Nat.bits_append_bit _ _ (by tauto), Nat.bits_append_bit _ _ (by tauto), c]
@[simp] theorem pair_bits (a b) : (pair a b).bits = frame a.bits b.bits :=
  (frameBits a.bits b).2
theorem pair_ne_zero (a b) : pair a b ≠ 0 := (frameBits a.bits b).1
theorem pair_size (a b) : (pair a b).size = 2*a.size + 1 + b.size := by
  rw [← Nat.size_eq_bits_len, pair_bits, frameLength,Nat.size_eq_bits_len,
    Nat.size_eq_bits_len]

/-- Parse as a frame. Arbitrary result on malformed. -/
def unpack : List Bool → List Bool × List Bool
  | false :: b :: l =>
    let (a,c) := unpack l
    (b::a,c)
  | true :: l => ([],l)
  | _ => ([],[])

theorem unpack_frame (l r) : unpack (frame l r) = (l,r) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih,unpack]

def unpair (n : ℕ) : ℕ × ℕ :=
  let (l,r) := unpack n.bits
  (val l,val r)

@[simp] theorem unpair_pair (a b) : unpair (pair a b) = (a,b) := by
  simp [unpair,unpack_frame,val_bits]

@[simp] theorem pair_inj {a b a' b'} :
    pair a b = pair a' b' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h => ?_, ?_⟩
  · simpa using congrArg unpair h
  · rintro ⟨rfl,rfl⟩; rfl

theorem mul_size (n m : ℕ) : (n*m).size ≤ n.size + m.size := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self n)
    (Nat.le_of_lt (Nat.lt_size_self m)) (by positivity)
theorem add_size (n m : ℕ) : (n+m).size ≤ max n.size m.size + 1 := by
  have a : n < 2^(max n.size m.size) := Nat.size_le.mp (le_max_left n.size m.size)
  have b : m < 2^(max n.size m.size) := Nat.size_le.mp (le_max_right n.size m.size)
  rw [Nat.size_le, pow_add]
  omega
theorem succ_size (n : ℕ) : (n+1).size ≤ n.size + 1 := by
  by_cases h : n = 0
  · subst n; simp
  · have e : 1 ≤ n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero h)
    simpa [max_eq_left,e] using add_size n 1
theorem pow_size (n m : ℕ) : (n^m).size ≤ 1 + m*n.size := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    apply le_trans (mul_size _ _)
    simp [Nat.add_mul]
    omega
theorem size_le_self (n : ℕ) : n.size ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => have := succ_size n; omega

@[simp] theorem bits_nil (n : ℕ) : n.bits = [] ↔ n = 0 := by
  refine ⟨fun e => ?_, fun e => by simp [e]⟩
  rw [← val_bits n,e]; rfl
end Bin
end Fifths

end OAI
