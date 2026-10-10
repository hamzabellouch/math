import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter

inductive Move
  | right
  | stay
  | left
  deriving DecidableEq, Repr

def update (b : ℕ) (m : Move) (β x y : ℕ) : ℕ × ℕ :=
  match m with
  | .right => (b * x + β, y / b)
  | .stay => (x, y - y % b + β)
  | .left => (x / b, x % b + b * β + b ^ 2 * (y / b))

theorem replace_digit (b y β : ℕ) :
    y - y % b + β = b * (y / b) + β := by
  have h := Nat.div_add_mod y b
  omega

def writtenDigit (b : ℕ) (m : Move) (p : ℕ × ℕ) : ℕ :=
  match m with
  | .right => p.1 % b
  | .stay => p.2 % b
  | .left => (p.2 / b) % b

def undo (b : ℕ) (m : Move) (α : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  match m with
  | .right => (p.1 / b, b * p.2 + α)
  | .stay => (p.1, b * (p.2 / b) + α)
  | .left => (b * p.1 + p.2 % b, b * (p.2 / b ^ 2) + α)

private theorem left_as_digits (b β x y : ℕ) :
    x % b + b * β + b ^ 2 * (y / b) = x % b + b * (β + b * (y / b)) := by
  ring

private theorem left_div (b β x y : ℕ) (hb : 0 < b) :
    (x % b + b * β + b ^ 2 * (y / b)) / b = β + b * (y / b) := by
  rw [left_as_digits, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt (Nat.mod_lt x hb)]
  omega

private theorem left_div_sq (b β x y : ℕ) (hb : 0 < b) (hβ : β < b) :
    (x % b + b * β + b ^ 2 * (y / b)) / b ^ 2 = y / b := by
  calc
    _ = ((x % b + b * β + b ^ 2 * (y / b)) / b) / b := by
      rw [Nat.div_div_eq_div_mul, pow_two]
    _ = y / b := by
      rw [left_div _ _ _ _ hb, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt hβ, zero_add]

private theorem left_mod (b β x y : ℕ) :
    (x % b + b * β + b ^ 2 * (y / b)) % b = x % b := by
  rw [left_as_digits, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem writtenDigit_update (b β x y : ℕ) (hb : 0 < b) (hβ : β < b) (m : Move) :
    writtenDigit b m (update b m β x y) = β := by
  cases m with
  | right => simp [writtenDigit, update, Nat.add_mod, Nat.mod_eq_of_lt hβ]
  | stay => simp [writtenDigit, update, replace_digit, Nat.add_mod, Nat.mod_eq_of_lt hβ]
  | left =>
    simp only [writtenDigit, update]
    rw [left_div _ _ _ _ hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ]

theorem undo_update (b β x y : ℕ) (hb : 0 < b) (hβ : β < b) (m : Move) :
    undo b m (y % b) (update b m β x y) = (x, y) := by
  cases m with
  | right =>
    simp only [undo, update]
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hβ, add_zero, Nat.div_add_mod]
  | stay =>
    simp only [undo, update, replace_digit]
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hβ, add_zero, Nat.div_add_mod]
  | left =>
    simp only [undo, update]
    rw [left_mod, left_div_sq _ _ _ _ hb hβ, Nat.div_add_mod, Nat.div_add_mod]

theorem written_eq_of_update_eq {b β₁ β₂ x₁ x₂ y₁ y₂ : ℕ}
    (hb : 0 < b) (hβ₁ : β₁ < b) (hβ₂ : β₂ < b) (m : Move)
    (h : update b m β₁ x₁ y₁ = update b m β₂ x₂ y₂) : β₁ = β₂ := by
  have eq := congrArg (writtenDigit b m) h
  simpa only [writtenDigit_update _ _ _ _ hb hβ₁,
    writtenDigit_update _ _ _ _ hb hβ₂] using eq

theorem stacks_eq_of_update_eq {b β x₁ x₂ y₁ y₂ : ℕ}
    (hb : 0 < b) (hβ : β < b) (m : Move) (hread : y₁ % b = y₂ % b)
    (h : update b m β x₁ y₁ = update b m β x₂ y₂) : (x₁, y₁) = (x₂, y₂) := by
  have eq := congrArg (undo b m (y₁ % b)) h
  rw [undo_update _ _ _ _ hb hβ, hread, undo_update _ _ _ _ hb hβ] at eq
  exact eq

structure Rule (σ : Type*) (b : ℕ) where
  target : σ
  written : Fin b
  move : Move

structure Configuration (σ : Type*) where
  state : σ
  leftStack : ℕ
  rightStack : ℕ
  deriving DecidableEq

def applyRule {σ : Type*} {b : ℕ} (r : Rule σ b) (c : Configuration σ) : Configuration σ :=
  let st := update b r.move r.written c.leftStack c.rightStack
  ⟨r.target, st.1, st.2⟩

def IncomingDirection {σ : Type*} {b : ℕ} (table : σ → Fin b → Option (Rule σ b)) : Prop :=
  ∀ i a j d r s, table i a = some r → table j d = some s →
    r.target = s.target → r.move = s.move

def IncomingRule {σ : Type*} {b : ℕ} (table : σ → Fin b → Option (Rule σ b)) : Prop :=
  ∀ i a j d r s, table i a = some r → table j d = some s →
    r.target = s.target → r.written = s.written → i = j ∧ a = d

theorem applyRule_injective {σ : Type*} {b : ℕ} (hb : 0 < b)
    (table : σ → Fin b → Option (Rule σ b))
    (hdir : IncomingDirection table) (hin : IncomingRule table)
    (c d : Configuration σ) (r s : Rule σ b)
    (hr : table c.state ⟨c.rightStack % b, Nat.mod_lt _ hb⟩ = some r)
    (hs : table d.state ⟨d.rightStack % b, Nat.mod_lt _ hb⟩ = some s)
    (hout : applyRule r c = applyRule s d) : c = d := by
  have ht : r.target = s.target := congrArg Configuration.state hout
  have hm : r.move = s.move := hdir _ _ _ _ _ _ hr hs ht
  have hxy : update b r.move r.written c.leftStack c.rightStack =
      update b s.move s.written d.leftStack d.rightStack := by
    have hx := congrArg Configuration.leftStack hout
    have hy := congrArg Configuration.rightStack hout
    exact Prod.ext hx hy
  rw [← hm] at hxy
  have hw : r.written = s.written := Fin.ext
    (written_eq_of_update_eq hb r.written.isLt s.written.isLt r.move hxy)
  obtain ⟨hq, ha⟩ := hin _ _ _ _ _ _ hr hs ht hw
  have hread : c.rightStack % b = d.rightStack % b := congrArg Fin.val ha
  rw [← hw] at hxy
  have hc := stacks_eq_of_update_eq hb r.written.isLt r.move hread hxy
  cases c
  cases d
  simp only [Configuration.mk.injEq] at *
  exact ⟨hq, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

theorem packed_lt {b β x B : ℕ} (hβ : β < b) (hx : x < B) :
    b * x + β < b * B := by
  calc
    b * x + β < b * x + b := Nat.add_lt_add_left hβ _
    _ = b * (x + 1) := by ring
    _ ≤ b * B := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hx)

theorem two_digits_lt {b β γ : ℕ} (hβ : β < b) (hγ : γ < b) :
    γ + b * β < b ^ 2 := by
  simpa [pow_two, add_comm] using packed_lt hγ hβ

theorem update_lt {b β x y B : ℕ} (hb : 0 < b) (hβ : β < b)
    (hx : x < B) (hy : y < B) (hB : b ∣ B) (m : Move) :
    (update b m β x y).1 < b * B ∧ (update b m β x y).2 < b * B := by
  have hB_le : B ≤ b * B := by
    simpa using Nat.mul_le_mul_right B (Nat.succ_le_of_lt hb)
  have hxsmall : x / b < b * B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hx hB_le)
  have hysmall : y / b < b * B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hy hB_le)
  obtain ⟨Q, rfl⟩ := hB
  have hydiv : y / b < Q :=
    (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using hy)
  cases m with
  | right => exact ⟨packed_lt hβ hx, hysmall⟩
  | stay =>
    refine ⟨lt_of_lt_of_le hx hB_le, ?_⟩
    change y - y % b + β < b * (b * Q)
    rw [replace_digit]
    exact lt_of_lt_of_le (packed_lt hβ hydiv) hB_le
  | left =>
    refine ⟨hxsmall, ?_⟩
    change x % b + b * β + b ^ 2 * (y / b) < b * (b * Q)
    have h := packed_lt (two_digits_lt hβ (Nat.mod_lt x hb)) hydiv
    calc
      x % b + b * β + b ^ 2 * (y / b) = b ^ 2 * (y / b) + (x % b + b * β) := by ring
      _ < b ^ 2 * Q := h
      _ = b * (b * Q) := by ring

def address (B i x y : ℕ) : ℕ := 1 + x + B * y + B ^ 2 * i

theorem address_packed (B i x y : ℕ) :
    address B i x y = 1 + (x + B * (y + B * i)) := by
  unfold address
  ring

@[simp] theorem address_sub_one (B i x y : ℕ) :
    address B i x y - 1 = x + B * (y + B * i) := by
  rw [address_packed, Nat.add_sub_cancel_left]

theorem address_pos (B i x y : ℕ) : 0 < address B i x y := by
  rw [address_packed]
  omega

theorem address_le {B i x y N : ℕ} (hi : i < N) (hx : x < B) (hy : y < B) :
    address B i x y ≤ N * B ^ 2 := by
  have hin : y + B * i < B * N := by simpa [add_comm] using packed_lt hy hi
  have hout : x + B * (y + B * i) < B * (B * N) := by
    simpa [add_comm] using packed_lt hx hin
  rw [address_packed]
  nlinarith

theorem address_decode_x {B i x y : ℕ} (hx : x < B) :
    (address B i x y - 1) % B = x := by
  rw [address_sub_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem address_decode_y {B i x y : ℕ} (hb : 0 < B) (hx : x < B) (hy : y < B) :
    ((address B i x y - 1) / B) % B = y := by
  rw [address_sub_one, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hx,
    zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]

theorem address_decode_state {B i x y : ℕ} (hb : 0 < B) (hx : x < B) (hy : y < B) :
    (address B i x y - 1) / B ^ 2 = i := by
  calc
    _ = ((address B i x y - 1) / B) / B := by
      rw [Nat.div_div_eq_div_mul, pow_two]
    _ = i := by
      rw [address_sub_one, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hx,
        zero_add, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hy, zero_add]

theorem address_injective {B i j x x' y y' : ℕ} (hb : 0 < B)
    (hx : x < B) (hx' : x' < B) (hy : y < B) (hy' : y' < B)
    (h : address B i x y = address B j x' y') : i = j ∧ x = x' ∧ y = y' := by
  have hi := congrArg (fun k => (k - 1) / B ^ 2) h
  have heqx := congrArg (fun k => (k - 1) % B) h
  have heqy := congrArg (fun k => ((k - 1) / B) % B) h
  rw [address_decode_state hb hx hy, address_decode_state hb hx' hy'] at hi
  rw [address_decode_x hx, address_decode_x hx'] at heqx
  rw [address_decode_y hb hx hy, address_decode_y hb hx' hy'] at heqy
  exact ⟨hi, heqx, heqy⟩

def capacity (b m n : ℕ) : ℕ := b ^ (m + n)

theorem capacity_succ (b m n : ℕ) :
    capacity b m (n + 1) = b * capacity b m n := by
  unfold capacity
  rw [← Nat.add_assoc, pow_succ, Nat.mul_comm]

theorem capacity_dvd {b m n : ℕ} (hm : 1 ≤ m) : b ∣ capacity b m n := by
  have h : 1 ≤ m + n := by omega
  exact dvd_pow_self b (by omega : m + n ≠ 0)

theorem update_capacity {b m n β x y : ℕ} (hb : 0 < b) (hm : 1 ≤ m)
    (hβ : β < b) (hx : x < capacity b m n) (hy : y < capacity b m n) (move : Move) :
    (update b move β x y).1 < capacity b m (n + 1) ∧
    (update b move β x y).2 < capacity b m (n + 1) := by
  rw [capacity_succ]
  exact update_lt hb hβ hx hy (capacity_dvd hm) move

theorem address_count_geometric (N b m n : ℕ) :
    N * capacity b m n ^ 2 = (N * capacity b m 0 ^ 2) * (b ^ 2) ^ n := by
  simp only [capacity, Nat.add_zero, pow_add, mul_pow, ← pow_mul]
  ring

end VelocityDetection.Stacks
end

end OAI
