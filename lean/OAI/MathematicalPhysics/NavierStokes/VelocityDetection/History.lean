import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.StacksLookup

namespace OAI

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks

structure Configuration (N : ℕ) where
  tape : Stacks.Configuration (Fin N)
  history : ℕ
  deriving DecidableEq

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))

def radix (N b : ℕ) : ℕ := N * b

def tag (c : Stacks.Configuration (Fin N)) : ℕ := b * c.state.val + c.rightStack % b

include hb in

theorem tag_lt (c : Stacks.Configuration (Fin N)) : tag (b := b) c < radix N b := by
  simpa only [tag, radix, Nat.mul_comm N] using
    (Stacks.packed_lt (Nat.mod_lt c.rightStack hb) c.state.isLt)

include hb in

theorem radix_pos (c : Stacks.Configuration (Fin N)) : 0 < radix N b :=
  Nat.mul_pos (Nat.zero_lt_of_lt c.state.isLt) hb

def applyRule (r : Rule (Fin N) b) (c : Configuration N) : Configuration N :=
  ⟨Stacks.applyRule r c.tape, radix N b * c.history + tag (b := b) c.tape⟩

include hb in

theorem recover_tag (r : Rule (Fin N) b) (c : Configuration N) :
    (applyRule r c).history % radix N b = tag (b := b) c.tape := by
  simp only [applyRule, Nat.add_mod, Nat.mul_mod_right, zero_add,
    Nat.mod_eq_of_lt (tag_lt hb c.tape)]

include hb in

theorem recover_history (r : Rule (Fin N) b) (c : Configuration N) :
    (applyRule r c).history / radix N b = c.history := by
  simp only [applyRule, Nat.mul_add_div (radix_pos hb c.tape),
    Nat.div_eq_of_lt (tag_lt hb c.tape), Nat.add_zero]

include hb in

theorem tag_decode_state (c : Stacks.Configuration (Fin N)) :
    tag (b := b) c / b = c.state.val := by
  simp only [tag, Nat.mul_add_div hb, Nat.div_eq_of_lt (Nat.mod_lt c.rightStack hb),
    Nat.add_zero]

theorem tag_decode_read (c : Stacks.Configuration (Fin N)) :
    tag (b := b) c % b = c.rightStack % b := by
  simp only [tag, Nat.add_mod, Nat.mul_mod_right, Nat.mod_mod, zero_add]

theorem applyRule_injective (c d : Configuration N) (r s : Rule (Fin N) b)
    (hr : Stacks.lookup hb table c.tape = some r)
    (hs : Stacks.lookup hb table d.tape = some s)
    (hout : applyRule r c = applyRule s d) : c = d := by
  have htag := congrArg (fun e : Configuration N => e.history % radix N b) hout
  simp only [recover_tag hb] at htag
  have hq : c.tape.state = d.tape.state := by
    apply Fin.ext
    simpa only [tag_decode_state hb] using congrArg (fun z => z / b) htag
  have ha : c.tape.rightStack % b = d.tape.rightStack % b := by
    simpa only [tag_decode_read] using congrArg (fun z => z % b) htag
  have hlookup : Stacks.lookup hb table c.tape = Stacks.lookup hb table d.tape := by
    simp only [Stacks.lookup, hq, ha]
  have hrs : r = s := Option.some.inj (hr.symm.trans (hlookup.trans hs))
  subst s
  have hxy : Stacks.update b r.move r.written c.tape.leftStack c.tape.rightStack =
      Stacks.update b r.move r.written d.tape.leftStack d.tape.rightStack :=
    Prod.ext (congrArg (fun e : Configuration N => e.tape.leftStack) hout)
      (congrArg (fun e : Configuration N => e.tape.rightStack) hout)
  have hst := Stacks.stacks_eq_of_update_eq hb r.written.isLt r.move ha hxy
  have hh := congrArg (fun e : Configuration N => e.history / radix N b) hout
  simp only [recover_history hb] at hh
  cases c with | mk ct ch =>
    cases d with | mk dt dh =>
      cases ct; cases dt
      simp only [Configuration.mk.injEq, Stacks.Configuration.mk.injEq] at *
      exact ⟨⟨hq, congrArg Prod.fst hst, congrArg Prod.snd hst⟩, hh⟩

def next (c : Configuration N) : Configuration N :=
  (Stacks.lookup hb table c.tape).elim c (fun r => applyRule r c)

@[simp] theorem next_tape (c : Configuration N) :
    (next hb table c).tape = Stacks.next hb table c.tape := by
  cases h : Stacks.lookup hb table c.tape <;> simp [next, Stacks.next, h, applyRule]

def orbit (c₀ : Configuration N) : ℕ → Configuration N
  | 0 => c₀
  | n + 1 => next hb table (orbit c₀ n)

@[simp] theorem orbit_zero (c₀ : Configuration N) : orbit hb table c₀ 0 = c₀ := rfl

@[simp] theorem orbit_succ (c₀ : Configuration N) (n : ℕ) :
    orbit hb table c₀ (n + 1) = next hb table (orbit hb table c₀ n) := rfl

@[simp] theorem orbit_tape (c₀ : Configuration N) (n : ℕ) :
    (orbit hb table c₀ n).tape = Stacks.orbit hb table c₀.tape n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit_succ, next_tape, ih, Stacks.orbit_succ]

def Halts (c₀ : Stacks.Configuration (Fin N)) : Prop :=
  ∃ n, Stacks.lookup hb table (Stacks.orbit hb table c₀ n) = none

theorem halts_iff (c₀ : Configuration N) :
    (∃ n, Stacks.lookup hb table (orbit hb table c₀ n).tape = none) ↔
      Halts hb table c₀.tape := by
  simp only [orbit_tape, Halts]

def Fits (B H : ℕ) (c : Configuration N) : Prop :=
  c.tape.leftStack < B ∧ c.tape.rightStack < B ∧ c.history < H

include hb in

theorem applyRule_fits {B H : ℕ} (hB : b ∣ B) (c : Configuration N)
    (hc : Fits B H c) (r : Rule (Fin N) b) :
    Fits (b * B) (radix N b * H) (applyRule r c) := by
  obtain ⟨hx, hy⟩ := Stacks.update_lt hb r.written.isLt hc.1 hc.2.1 hB r.move
  exact ⟨hx, hy, Stacks.packed_lt (tag_lt hb c.tape) hc.2.2⟩

theorem next_fits {B H : ℕ} (hB : b ∣ B) (c : Configuration N)
    (hc : Fits B H c) : Fits (b * B) (radix N b * H) (next hb table c) := by
  cases h : Stacks.lookup hb table c.tape with
  | none =>
    simp only [next, h, Option.elim_none]
    have hB' : B ≤ b * B := by simpa using Nat.mul_le_mul_right B hb
    have hH : H ≤ radix N b * H := by
      simpa using Nat.mul_le_mul_right H (radix_pos hb c.tape)
    exact ⟨hc.1.trans_le hB', hc.2.1.trans_le hB', hc.2.2.trans_le hH⟩
  | some r =>
    simp only [next, h, Option.elim_some]
    exact applyRule_fits hb hB c hc r

theorem orbit_fits {m : ℕ} (hm : 1 ≤ m) (c₀ : Stacks.Configuration (Fin N))
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0) (n : ℕ) :
    Fits (capacity b m n) (radix N b ^ n) (orbit hb table ⟨c₀, 0⟩ n) := by
  induction n with
  | zero => exact ⟨hc₀.1, hc₀.2, by simp⟩
  | succ n ih =>
    rw [orbit_succ, capacity_succ, pow_succ']
    exact next_fits hb table (capacity_dvd hm) _ ih

def packedState (c : Configuration N) : ℕ := N * c.history + c.tape.state.val

theorem packedState_lt {H : ℕ} {c : Configuration N} (hc : c.history < H) :
    packedState c < N * H := Stacks.packed_lt c.tape.state.isLt hc

theorem packedState_mod (c : Configuration N) : packedState c % N = c.tape.state.val := by
  simp [packedState, Nat.add_mod, Nat.mod_eq_of_lt c.tape.state.isLt]

theorem packedState_div (c : Configuration N) : packedState c / N = c.history := by
  simp only [packedState, Nat.mul_add_div (Nat.zero_lt_of_lt c.tape.state.isLt),
    Nat.div_eq_of_lt c.tape.state.isLt, add_zero]

def address (B : ℕ) (c : Configuration N) : ℕ :=
  Stacks.address B (packedState c) c.tape.leftStack c.tape.rightStack

theorem address_le {B H : ℕ} {c : Configuration N} (hc : Fits B H c) :
    address B c ≤ (N * H) * B ^ 2 :=
  Stacks.address_le (packedState_lt hc.2.2) hc.1 hc.2.1

theorem address_injective {B H : ℕ} (hB : 0 < B) {c d : Configuration N}
    (hc : Fits B H c) (hd : Fits B H d) (h : address B c = address B d) : c = d := by
  obtain ⟨hq, hx, hy⟩ :=
    Stacks.address_injective hB hc.1 hd.1 hc.2.1 hd.2.1 h
  have hs : c.tape.state = d.tape.state := by
    apply Fin.ext
    simpa only [packedState_mod] using congrArg (fun a => a % N) hq
  have hh : c.history = d.history := by
    simpa only [packedState_div] using congrArg (fun a => a / N) hq
  cases c with | mk ct ch =>
    cases d with | mk dt dh =>
      cases ct; cases dt
      simp only [Configuration.mk.injEq, Stacks.Configuration.mk.injEq] at *
      exact ⟨⟨hs, hx, hy⟩, hh⟩

theorem address_count_geometric (m n : ℕ) :
    (N * radix N b ^ n) * capacity b m n ^ 2 =
      (N * capacity b m 0 ^ 2) * (b ^ 2 * radix N b) ^ n := by
  simp only [capacity, Nat.add_zero, pow_add, mul_pow, ← pow_mul]
  ring

abbrev Box (N B H : ℕ) := Fin N × Fin B × Fin B × Fin H

def config {B H : ℕ} (c : Box N B H) : Configuration N :=
  ⟨⟨c.1, c.2.1, c.2.2.1⟩, c.2.2.2⟩

theorem config_fits {B H : ℕ} (c : Box N B H) : Fits B H (config c) :=
  ⟨c.2.1.isLt, c.2.2.1.isLt, c.2.2.2.isLt⟩

theorem config_injective {B H : ℕ} : Function.Injective (@config N B H) := by
  intro c d h
  exact Prod.ext (congrArg (fun e : Configuration N => e.tape.state) h)
    (Prod.ext (Fin.ext (congrArg (fun e : Configuration N => e.tape.leftStack) h))
      (Prod.ext (Fin.ext (congrArg (fun e : Configuration N => e.tape.rightStack) h))
        (Fin.ext (congrArg Configuration.history h))))

def Active (B H : ℕ) := {c : Box N B H // (Stacks.lookup hb table (config c).tape).isSome}

instance {B H : ℕ} : Fintype (Active hb table B H) := by
  unfold Active
  infer_instance

def rule {B H : ℕ} (c : Active hb table B H) : Rule (Fin N) b :=
  (Stacks.lookup hb table (config c.val).tape).get c.property

theorem lookup_rule {B H : ℕ} (c : Active hb table B H) :
    Stacks.lookup hb table (config c.val).tape = some (rule hb table c) :=
  (Option.some_get c.property).symm

def target {B H : ℕ} (c : Active hb table B H) : Configuration N :=
  applyRule (rule hb table c) (config c.val)

def sourceAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address B (config c.val)

def targetAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address (b * B) (target hb table c)

theorem sourceAddress_injective {B H : ℕ} (hB : 0 < B) :
    Function.Injective (@sourceAddress N b hb table B H) := by
  intro c d h
  exact Subtype.ext (config_injective
    (address_injective hB (config_fits c.val) (config_fits d.val) h))

theorem target_fits {B H : ℕ} (hB : b ∣ B) (c : Active hb table B H) :
    Fits (b * B) (radix N b * H) (target hb table c) :=
  applyRule_fits hb hB _ (config_fits c.val) _

theorem targetAddress_injective {B H : ℕ} (hBpos : 0 < B) (hBdiv : b ∣ B) :
    Function.Injective (@targetAddress N b hb table B H) := by
  intro c d h
  have ht := address_injective (Nat.mul_pos hb hBpos)
    (target_fits hb table hBdiv c) (target_fits hb table hBdiv d) h
  have hc := applyRule_injective hb table _ _ _ _ (lookup_rule hb table c) (lookup_rule hb table d) ht
  exact Subtype.ext (config_injective hc)

theorem sourceAddress_count {B H : ℕ} (c : Active hb table B H) :
    sourceAddress hb table c ≤ (N * H) * B ^ 2 := address_le (config_fits c.val)

theorem targetAddress_count {B H : ℕ} (hB : b ∣ B) (c : Active hb table B H) :
    targetAddress hb table c ≤ (N * (radix N b * H)) * (b * B) ^ 2 :=
  address_le (target_fits hb table hB c)

end VelocityDetection.History
end

end OAI
