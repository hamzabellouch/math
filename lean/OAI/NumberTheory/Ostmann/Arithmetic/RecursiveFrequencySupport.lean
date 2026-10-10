import OAI.NumberTheory.Ostmann.Construction.RecursiveTransferWeight
import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyTree

namespace OAI

/-! # The original leaf-frequency cutoffs in the recursive squared weights -/

namespace Ostmann

open scoped Classical

def frequencyTreeMap {A B : Type} (f : A → B) : (n : ℕ) → FrequencyTree A n → FrequencyTree B n
  | 0, x => f x
  | n + 1, x => (f x.1, frequencyTreeMap f n x.2.1, frequencyTreeMap f n x.2.2)

theorem frequencyRoot_map {A B : Type} (f : A → B) (n : ℕ) (x : FrequencyTree A n) :
    frequencyRoot n (frequencyTreeMap f n x) = f (frequencyRoot n x) := by
  cases n <;> rfl

theorem frequencyLeafWeight_map {A B : Type} (f : A → B) (W : B → ℝ)
    (n : ℕ) (x : FrequencyTree A n) :
    frequencyLeafWeight W n (frequencyTreeMap f n x) = frequencyLeafWeight (fun a => W (f a)) n x := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg₂ (· * ·) (ih x.2.1) (ih x.2.2)

theorem recursiveTransferWeight_children_nonzero {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (σ : State)
    (t : FrequencyTree ℤ (n + 1))
    (ht : recursiveTransferWeight sys leaf cutoff (n + 1) σ t ≠ 0) :
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ∧
      recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 ∧
      recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
  let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
  by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
  · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
    refine ⟨hP, ?_, ?_⟩
    · intro hz
      change recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 = 0 at hz
      exact ht (by rw [hz, mul_zero, zero_mul])
    · intro hz
      change recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 = 0 at hz
      exact ht (by rw [hz, star_zero, mul_zero])
  · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false]))

theorem recursiveTransferWeight_leaf_cutoff {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V n : ℕ)
    (hleaf : ∀ σ v, leaf σ v ≠ 0 → v.natAbs ≤ V) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    frequencyLeafWeight (fun v : ℤ => if v.natAbs ≤ V then (1 : ℝ) else 0) n t = 1 := by
  induction n generalizing σ with
  | zero => exact ite_eq_left (hleaf σ t ht)
  | succ n ih =>
    obtain ⟨_, hL, hR⟩ := recursiveTransferWeight_children_nonzero sys leaf cutoff n σ t ht
    change frequencyLeafWeight _ n t.2.1 * frequencyLeafWeight _ n t.2.2 = 1
    rw [ih _ _ hL, ih _ _ hR, mul_one]

/-- The square bound retains the actual leaf-frequency indicator. No
extra leaf frequencies are introduced when support restrictions are dropped. -/
theorem recursiveTransferWeight_square_with_leaf_cutoff {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ B)
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (V : ℕ) (hleaf : ∀ σ v, leaf σ v ≠ 0 → v.natAbs ≤ V)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) :
    ‖recursiveTransferWeight sys leaf cutoff n σ (frequencyTreeMap Subtype.val n t)‖ ^ 2 ≤
      B ^ (2 ^ n) * frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  by_cases ht : recursiveTransferWeight sys leaf cutoff n σ (frequencyTreeMap Subtype.val n t) = 0
  · simp only [ht, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (pow_nonneg hB _) (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)
  · have hl := recursiveTransferWeight_leaf_cutoff sys leaf cutoff V n hleaf σ
      (frequencyTreeMap Subtype.val n t) ht
    rw [frequencyLeafWeight_map] at hl
    change frequencyLeafWeight (singleFrequencyLeaf S V) n t = 1 at hl
    rw [hl, mul_one]
    exact recursiveTransferWeight_square_le sys leaf cutoff B hB hsize hcut n σ _

end Ostmann

end OAI
