import OAI.Combinatorics.EditApproximation.Geometry.GatheredLocalStep
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem mixedRadix_injective {radix lo lo' hi hi' : ℕ}
    (hlo : lo < radix) (hlo' : lo' < radix)
    (heq : lo + radix * hi = lo' + radix * hi') : lo = lo' ∧ hi = hi' := by
  have hmod := congrArg (fun n => n % radix) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlo'] at hmod
  refine ⟨hmod, ?_⟩
  apply Nat.mul_left_cancel (by omega : 0 < radix)
  omega



theorem childInputCode_injective (M n : ℕ) :
    Function.Injective (@childInputCode M n) := by
  rintro ⟨i, q⟩ ⟨i', q'⟩ heq
  obtain ⟨hi, hq⟩ := mixedRadix_injective i.isLt i'.isLt heq
  have hqlo : q.lo < n + 1 := by have := q.ordered.trans q.valid; omega
  have hqlo' : q'.lo < n + 1 := by have := q'.ordered.trans q'.valid; omega
  obtain ⟨hlo, hhi⟩ := mixedRadix_injective hqlo hqlo' hq
  have hqeq : q = q' := by cases q; cases q'; cases hlo; cases hhi; rfl
  exact Prod.ext (Fin.ext hi) hqeq

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

def childInputBits (M n : ℕ) : ℕ := Nat.clog 2 (M * (n + 1) ^ 2 + 1)

theorem childInputCode_fits {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < 2 ^ childInputBits M n := by
  exact (childInputCode_bound input).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

theorem childInputBinaryKey_injective (M n : ℕ) :
    Function.Injective (fun input : Fin M × TargetInterval n =>
      binaryMemoKey (childInputBits M n) (childInputCode input)) := by
  intro input other heq
  apply childInputCode_injective M n
  exact binaryMemoKey_injective _ (childInputCode_fits input) (childInputCode_fits other) heq

theorem childInputBits_le (M n H : ℕ) (hM : M ≤ 2 ^ H) (hn : n + 1 ≤ 2 ^ H) :
    childInputBits M n ≤ 3 * H + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  have hproduct : M * (n + 1) ^ 2 ≤ 2 ^ (3 * H) := by
    calc
      _ ≤ 2 ^ H * (2 ^ H) ^ 2 := Nat.mul_le_mul hM (Nat.pow_le_pow_left hn 2)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hone : 1 ≤ 2 ^ (3 * H) := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  calc
    _ ≤ 2 ^ (3 * H) + 2 ^ (3 * H) := Nat.add_le_add hproduct hone
    _ = 2 ^ (3 * H + 1) := by rw [pow_succ]; omega

end EditApproximation

end OAI
