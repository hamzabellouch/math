import OAI.Algebra.FormulaHitting.BitModel
import Mathlib.Data.Nat.Size
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

namespace NCHitting.BitArithmetic

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def parity (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)
def borrow (a b c : Bool) : Bool := ((!a) && b) || ((!a) && c) || (b && c)
def equalStep (a b c : Bool) : Bool := (a == b) && c

theorem fullAdder_identity (a b c : Bool) :
    (parity a b c).toNat + 2 * (carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

theorem fullSubtractor_identity (a b c : Bool) :
    (parity a b c).toNat + b.toNat + c.toNat = a.toNat + 2 * (borrow a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

structure WordRun where
  bits : List Bool
  steps : ℕ

def trim : List Bool → List Bool
  | [] => []
  | b :: bs =>
      let t := trim bs
      if t = [] ∧ b = false then [] else b :: t

def trimSteps : List Bool → ℕ
  | [] => 1
  | _ :: bs => trimSteps bs + 3

theorem trimSteps_eq (bs : List Bool) : trimSteps bs = 3 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [trimSteps, List.length_cons, ih]; omega

@[simp] theorem value_trim (bs : List Bool) : value (trim bs) = value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [trim]
    split_ifs with h
    · rcases h with ⟨ht, rfl⟩
      simp only [ht, value] at ih
      simp [value, ← ih]
    · simp only [value, ih]

theorem bits_value (bs : List Bool) : (value bs).bits = trim bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hzero : value bs = 0
    · have ht : trim bs = [] := by rw [← ih, hzero]; rfl
      cases b <;> simp [value, hzero, trim, ht]
    · have ht : trim bs ≠ [] := by
        intro h
        have := value_trim bs
        rw [h] at this
        exact hzero this.symm
      have hbit : b.toNat + 2 * value bs = Nat.bit b (value bs) := by
        rw [Nat.bit_val]
        omega
      rw [value, hbit, Nat.bits_append_bit _ _ (fun h => (hzero h).elim), ih]
      simp [trim, ht]

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, value, ih, Nat.bit_val]
    omega

theorem trim_length (bs : List Bool) : (trim bs).length = (value bs).size := by
  rw [← bits_value, Nat.size_eq_bits_len]

def addRaw : List Bool → List Bool → Bool → WordRun
  | [], [], c => ⟨if c then [true] else [], 3⟩
  | a :: xs, [], c =>
      let r := addRaw xs [] (carry a false c)
      ⟨parity a false c :: r.bits, r.steps + 5⟩
  | [], b :: ys, c =>
      let r := addRaw [] ys (carry false b c)
      ⟨parity false b c :: r.bits, r.steps + 5⟩
  | a :: xs, b :: ys, c =>
      let r := addRaw xs ys (carry a b c)
      ⟨parity a b c :: r.bits, r.steps + 5⟩

theorem addRaw_value (xs ys : List Bool) (c : Bool) :
    value (addRaw xs ys c).bits = value xs + value ys + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addRaw, value]
    | cons b ys ih =>
      have h := fullAdder_identity false b c
      simp only [addRaw, value, ih]
      simp only [Bool.toNat_false] at h
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := fullAdder_identity a false c
      simp only [addRaw, value, ih]
      simp only [Bool.toNat_false] at h
      omega
    | cons b ys =>
      have h := fullAdder_identity a b c
      simp only [addRaw, value, ih]
      omega

theorem addRaw_length (xs ys : List Bool) (c : Bool) :
    (addRaw xs ys c).bits.length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addRaw]
    | cons b ys ih =>
      have h := ih (carry false b c)
      simp only [addRaw, List.length_cons, List.length_nil, Nat.zero_max] at h ⊢
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (carry a false c)
      simp only [addRaw, List.length_cons, List.length_nil, Nat.max_zero] at h ⊢
      omega
    | cons b ys =>
      have h := ih ys (carry a b c)
      simp only [addRaw, List.length_cons] at h ⊢
      omega

theorem addRaw_steps (xs ys : List Bool) (c : Bool) :
    (addRaw xs ys c).steps ≤ 5 * (xs.length + ys.length) + 3 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [addRaw]
    | cons b ys ih =>
      have h := ih (carry false b c)
      simp only [addRaw, List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (carry a false c)
      simp only [addRaw, List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      have h := ih ys (carry a b c)
      simp only [addRaw, List.length_cons] at h ⊢
      omega

def add (xs ys : List Bool) : WordRun :=
  let raw := addRaw xs ys false
  ⟨trim raw.bits, raw.steps + trimSteps raw.bits⟩

theorem add_value (xs ys : List Bool) : value (add xs ys).bits = value xs + value ys := by
  simp [add, addRaw_value]

theorem add_steps (xs ys : List Bool) :
    (add xs ys).steps ≤ 8 * (xs.length + ys.length) + 7 := by
  have hs := addRaw_steps xs ys false
  have hl := addRaw_length xs ys false
  simp only [add, trimSteps_eq]
  omega

structure BoolRun where
  bit : Bool
  steps : ℕ

def lessRaw : List Bool → List Bool → Bool → BoolRun
  | [], [], c => ⟨c, 2⟩
  | a :: xs, [], c =>
      let r := lessRaw xs [] (borrow a false c)
      ⟨r.bit, r.steps + 3⟩
  | [], b :: ys, c =>
      let r := lessRaw [] ys (borrow false b c)
      ⟨r.bit, r.steps + 3⟩
  | a :: xs, b :: ys, c =>
      let r := lessRaw xs ys (borrow a b c)
      ⟨r.bit, r.steps + 3⟩

theorem lessRaw_value (xs ys : List Bool) (c : Bool) :
    (lessRaw xs ys c).bit = true ↔ value xs < value ys + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [lessRaw, value]
    | cons b ys ih =>
      simp only [lessRaw, ih, value]
      cases b <;> cases c <;> simp [borrow]
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [lessRaw, ih, value]
      cases a <;> cases c <;> simp [borrow]
    | cons b ys =>
      simp only [lessRaw, ih, value]
      cases a <;> cases b <;> cases c <;> simp [borrow] <;> omega

theorem lessRaw_steps (xs ys : List Bool) (c : Bool) :
    (lessRaw xs ys c).steps ≤ 3 * (xs.length + ys.length) + 2 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [lessRaw]
    | cons b ys ih =>
      have h := ih (borrow false b c)
      simp only [lessRaw, List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (borrow a false c)
      simp only [lessRaw, List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      have h := ih ys (borrow a b c)
      simp only [lessRaw, List.length_cons] at h ⊢
      omega

def equalRaw : List Bool → List Bool → Bool → BoolRun
  | [], [], c => ⟨c, 2⟩
  | a :: xs, [], c =>
      let r := equalRaw xs [] (equalStep a false c)
      ⟨r.bit, r.steps + 3⟩
  | [], b :: ys, c =>
      let r := equalRaw [] ys (equalStep false b c)
      ⟨r.bit, r.steps + 3⟩
  | a :: xs, b :: ys, c =>
      let r := equalRaw xs ys (equalStep a b c)
      ⟨r.bit, r.steps + 3⟩

theorem equalRaw_value (xs ys : List Bool) (c : Bool) :
    (equalRaw xs ys c).bit = true ↔ value xs = value ys ∧ c = true := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [equalRaw, value]
    | cons b ys ih =>
      simp only [equalRaw, ih, value]
      cases b <;> cases c <;> simp [equalStep] <;> omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [equalRaw, ih, value]
      cases a <;> cases c <;> simp [equalStep]
    | cons b ys =>
      simp only [equalRaw, ih, value]
      cases a <;> cases b <;> cases c <;> simp [equalStep] <;> omega

theorem equalRaw_steps (xs ys : List Bool) (c : Bool) :
    (equalRaw xs ys c).steps ≤ 3 * (xs.length + ys.length) + 2 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [equalRaw]
    | cons b ys ih =>
      have h := ih (equalStep false b c)
      simp only [equalRaw, List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (equalStep a false c)
      simp only [equalRaw, List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      have h := ih ys (equalStep a b c)
      simp only [equalRaw, List.length_cons] at h ⊢
      omega

structure SubRun extends WordRun where
  finalBorrow : Bool

def subRaw : List Bool → List Bool → Bool → SubRun
  | [], [], c => ⟨⟨[], 2⟩, c⟩
  | a :: xs, [], c =>
      let r := subRaw xs [] (borrow a false c)
      ⟨⟨parity a false c :: r.bits, r.steps + 5⟩, r.finalBorrow⟩
  | [], b :: ys, c =>
      let r := subRaw [] ys (borrow false b c)
      ⟨⟨parity false b c :: r.bits, r.steps + 5⟩, r.finalBorrow⟩
  | a :: xs, b :: ys, c =>
      let r := subRaw xs ys (borrow a b c)
      ⟨⟨parity a b c :: r.bits, r.steps + 5⟩, r.finalBorrow⟩

theorem subRaw_borrow (xs ys : List Bool) (c : Bool) :
    (subRaw xs ys c).finalBorrow = (lessRaw xs ys c).bit := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw, lessRaw]
    | cons b ys ih => simp only [subRaw, lessRaw, ih]
  | cons a xs ih =>
    cases ys <;> simp only [subRaw, lessRaw, ih]

theorem subRaw_value (xs ys : List Bool) (c : Bool) :
    value (subRaw xs ys c).bits + value ys + c.toNat =
      value xs + 2 ^ (max xs.length ys.length) * (subRaw xs ys c).finalBorrow.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw, value]
    | cons b ys ih =>
      have h := ih (borrow false b c)
      have hb := fullSubtractor_identity false b c
      simp only [subRaw, value, List.length_nil, List.length_cons, Nat.zero_max,
        pow_succ, Bool.toNat_false, Nat.zero_add, Nat.mul_assoc] at h hb ⊢
      nlinarith
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (borrow a false c)
      have hb := fullSubtractor_identity a false c
      simp only [subRaw, value, List.length_nil, List.length_cons, Nat.max_zero,
        pow_succ, Bool.toNat_false, Nat.add_zero, Nat.mul_assoc] at h hb ⊢
      nlinarith
    | cons b ys =>
      have h := ih ys (borrow a b c)
      have hb := fullSubtractor_identity a b c
      have hm : max (xs.length + 1) (ys.length + 1) = max xs.length ys.length + 1 := by omega
      simp only [subRaw, value, List.length_cons, hm,
        pow_succ, Nat.mul_assoc] at h hb ⊢
      nlinarith

theorem subRaw_length (xs ys : List Bool) (c : Bool) :
    (subRaw xs ys c).bits.length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw]
    | cons b ys ih => simp [subRaw, ih]
  | cons a xs ih => cases ys <;> simp [subRaw, ih, max_add_add_right]

theorem subRaw_steps (xs ys : List Bool) (c : Bool) :
    (subRaw xs ys c).steps ≤ 5 * (xs.length + ys.length) + 2 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw]
    | cons b ys ih =>
      have h := ih (borrow false b c)
      simp only [subRaw, List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h := ih [] (borrow a false c)
      simp only [subRaw, List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      have h := ih ys (borrow a b c)
      simp only [subRaw, List.length_cons] at h ⊢
      omega

def sub (xs ys : List Bool) : WordRun :=
  let raw := subRaw xs ys false
  if raw.finalBorrow then ⟨[], raw.steps + 1⟩
  else ⟨trim raw.bits, raw.steps + 1 + trimSteps raw.bits⟩

theorem sub_value (xs ys : List Bool) : value (sub xs ys).bits = value xs - value ys := by
  have h := subRaw_value xs ys false
  have hb := lessRaw_value xs ys false
  rw [← subRaw_borrow] at hb
  cases hcase : (subRaw xs ys false).finalBorrow with
  | false =>
    simp [sub, hcase, value_trim]
    simp [hcase] at h
    omega
  | true =>
    have hlt : value xs < value ys := by simpa [hcase] using hb.mp hcase
    simp [sub, hcase, value, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]

theorem sub_steps (xs ys : List Bool) :
    (sub xs ys).steps ≤ 8 * (xs.length + ys.length) + 4 := by
  have hs := subRaw_steps xs ys false
  have hl := subRaw_length xs ys false
  unfold sub
  dsimp only
  split <;> simp only [trimSteps_eq] <;> omega

def mulRaw : List Bool → List Bool → WordRun
  | [], _ => ⟨[], 1⟩
  | b :: xs, ys =>
      let r := mulRaw xs ys
      if b then
        let a := addRaw ys (false :: r.bits) false
        ⟨a.bits, r.steps + a.steps + 3⟩
      else ⟨false :: r.bits, r.steps + 3⟩

theorem mulRaw_value (xs ys : List Bool) :
    value (mulRaw xs ys).bits = value xs * value ys := by
  induction xs with
  | nil => simp [mulRaw, value]
  | cons b xs ih =>
    cases b <;> simp [mulRaw, value, addRaw_value, ih] <;> ring

theorem mulRaw_length (xs ys : List Bool) :
    (mulRaw xs ys).bits.length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mulRaw]
  | cons b xs ih =>
    have ha := addRaw_length ys (false :: (mulRaw xs ys).bits) false
    cases b <;> simp only [mulRaw, Bool.false_eq_true, ite_false, ite_true,
      List.length_cons] at * <;> omega

theorem mulRaw_steps (xs ys : List Bool) :
    (mulRaw xs ys).steps ≤ 10 * xs.length * (xs.length + ys.length + 2) + 1 := by
  induction xs with
  | nil => simp [mulRaw]
  | cons b xs ih =>
    have ha := addRaw_steps ys (false :: (mulRaw xs ys).bits) false
    have hl := mulRaw_length xs ys
    cases b <;> simp only [mulRaw, Bool.false_eq_true, ite_false, ite_true,
      List.length_cons] at * <;> nlinarith

def mul (xs ys : List Bool) : WordRun :=
  let raw := mulRaw xs ys
  ⟨trim raw.bits, raw.steps + trimSteps raw.bits⟩

theorem mul_value (xs ys : List Bool) : value (mul xs ys).bits = value xs * value ys := by
  simp [mul, mulRaw_value]

theorem mul_steps (xs ys : List Bool) :
    (mul xs ys).steps ≤ 10 * xs.length * (xs.length + ys.length + 2) +
      6 * xs.length + 3 * ys.length + 2 := by
  have hs := mulRaw_steps xs ys
  have hl := mulRaw_length xs ys
  simp only [mul, trimSteps_eq]
  omega

def addNat (a b : ℕ) : WordRun := add a.bits b.bits
def subNat (a b : ℕ) : WordRun := sub a.bits b.bits
def mulNat (a b : ℕ) : WordRun := mul a.bits b.bits
def lessNat (a b : ℕ) : BoolRun := lessRaw a.bits b.bits false
def equalNat (a b : ℕ) : BoolRun := equalRaw a.bits b.bits true
def oddNat (a : ℕ) : BoolRun := ⟨a.bits.headD false, 2⟩

theorem oddNat_value (a : ℕ) : (oddNat a).bit.toNat = a % 2 := by
  have hhead : a.bits.headD false = a.bits.headI := by cases a.bits <;> rfl
  change (a.bits.headD false).toNat = a % 2
  rw [hhead, ← Nat.bodd_eq_bits_head]
  exact (Nat.mod_two_of_bodd a).symm

theorem oddNat_eq (a : ℕ) : (oddNat a).bit = decide (a % 2 = 1) := by
  have h := oddNat_value a
  cases hb : (oddNat a).bit <;> simp [hb] at h ⊢ <;> omega

theorem addNat_value (a b : ℕ) : (addNat a b).bits = (a + b).bits := by
  simp only [addNat, add, ← bits_value, addRaw_value, value_bits, Bool.toNat_false, Nat.add_zero]

theorem mulNat_value (a b : ℕ) : (mulNat a b).bits = (a * b).bits := by
  simp only [mulNat, mul, ← bits_value, mulRaw_value, value_bits]

theorem subNat_value (a b : ℕ) : (subNat a b).bits = (a - b).bits := by
  have hv := sub_value a.bits b.bits
  simp only [value_bits] at hv
  unfold subNat sub
  dsimp only
  split
  · have hzero : a - b = 0 := by simpa [sub, value, *] using hv.symm
    simp [hzero]
  · have hraw : value (subRaw a.bits b.bits false).bits = a - b := by
      simpa [sub, *] using hv
    change trim (subRaw a.bits b.bits false).bits = (a - b).bits
    rw [← bits_value, hraw]

theorem lessNat_value (a b : ℕ) : (lessNat a b).bit = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr
  simp [lessNat, lessRaw_value, value_bits]

theorem equalNat_value (a b : ℕ) : (equalNat a b).bit = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp [equalNat, equalRaw_value, value_bits]

theorem addNat_steps (a b : ℕ) : (addNat a b).steps ≤ (BitModel.addCost a b) ^ 2 := by
  have h := add_steps a.bits b.bits
  simp only [Nat.size_eq_bits_len] at h
  unfold addNat BitModel.addCost BitModel.width
  nlinarith [sq_nonneg (a.size + b.size : ℤ)]

theorem subNat_steps (a b : ℕ) : (subNat a b).steps ≤ (BitModel.addCost a b) ^ 2 := by
  have h := sub_steps a.bits b.bits
  simp only [Nat.size_eq_bits_len] at h
  unfold subNat BitModel.addCost BitModel.width
  nlinarith [sq_nonneg (a.size + b.size : ℤ)]

theorem lessNat_steps (a b : ℕ) : (lessNat a b).steps ≤ (BitModel.compareCost a b) ^ 2 := by
  have h := lessRaw_steps a.bits b.bits false
  simp only [Nat.size_eq_bits_len] at h
  unfold lessNat BitModel.compareCost BitModel.width
  nlinarith [sq_nonneg (a.size + b.size : ℤ)]

theorem equalNat_steps (a b : ℕ) : (equalNat a b).steps ≤ (BitModel.compareCost a b) ^ 2 := by
  have h := equalRaw_steps a.bits b.bits true
  simp only [Nat.size_eq_bits_len] at h
  unfold equalNat BitModel.compareCost BitModel.width
  nlinarith [sq_nonneg (a.size + b.size : ℤ)]

theorem mulNat_steps (a b : ℕ) : (mulNat a b).steps ≤ (BitModel.mulCost a b) ^ 2 := by
  have h := mul_steps a.bits b.bits
  simp only [Nat.size_eq_bits_len] at h
  let W := (a.size + 1) * (b.size + 1)
  have hW : 1 ≤ W := by
    exact Nat.mul_le_mul (show 1 ≤ a.size + 1 by omega) (show 1 ≤ b.size + 1 by omega)
  have ha : a.size ≤ W := by dsimp [W]; nlinarith
  have hb : b.size ≤ W := by dsimp [W]; nlinarith
  have hs : a.size + b.size + 2 ≤ 2 * W := by dsimp [W]; nlinarith
  have hp : a.size * (a.size + b.size + 2) ≤ W * (2 * W) :=
    Nat.mul_le_mul ha hs
  change (mul a.bits b.bits).steps ≤ (8 * (a.size + 1) * (b.size + 1)) ^ 2
  have he : 8 * (a.size + 1) * (b.size + 1) = 8 * W := by dsimp [W]; ring
  rw [he]
  nlinarith

end NCHitting.BitArithmetic

end OAI
