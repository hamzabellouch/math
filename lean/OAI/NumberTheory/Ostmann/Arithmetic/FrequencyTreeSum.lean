import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Summing internal frequencies from the root downwards -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def FrequencyTree (A : Type) : ℕ → Type
  | 0 => A
  | n + 1 => A × FrequencyTree A n × FrequencyTree A n

instance frequencyTreeFintype (A : Type) [Fintype A] (n : ℕ) :
    Fintype (FrequencyTree A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype A)
  | succ n ih => exact @instFintypeProd _ _ _ (@instFintypeProd _ _ ih ih)

@[implicit_reducible] def frequencyRoot {A : Type} : (n : ℕ) → FrequencyTree A n → A
  | 0, x => x
  | _ + 1, x => x.1

noncomputable def frequencyTreeWeight {A : Type} (K : A → A → A → ℝ) (W : A → ℝ) :
    (n : ℕ) → FrequencyTree A n → ℝ
  | 0, x => W x
  | n + 1, x => K x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) *
      frequencyTreeWeight K W n x.2.1 * frequencyTreeWeight K W n x.2.2

theorem frequencyTreeWeight_nonneg {A : Type} (K : A → A → A → ℝ) (W : A → ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyTreeWeight K W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (mul_nonneg (hK _ _ _) (ih x.2.1)) (ih x.2.2)

/-- Each pair of parent frequencies is summed before either child pair.
Only the leaf mass remains after all internal frequencies are eliminated. -/
theorem frequencyTree_sum_le {A : Type} [Fintype A]
    (K : A → A → A → ℝ) (W : A → ℝ) (C : ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a) (hC : 0 ≤ C)
    (hsum : ∀ b c, ∑ a : A, K a b c ≤ C) (n : ℕ) :
    (∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) ≤
      C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) := by
  induction n with
  | zero => simp [FrequencyTree, frequencyTreeWeight]
  | succ n ih =>
    have hweight := frequencyTreeWeight_nonneg K W hK hW n
    have hsum0 : 0 ≤ ∑ x : FrequencyTree A n, frequencyTreeWeight K W n x :=
      Finset.sum_nonneg fun x _ => hweight x
    have hbound0 : 0 ≤ C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) :=
      mul_nonneg (pow_nonneg hC _) (pow_nonneg (Finset.sum_nonneg fun a _ => hW a) _)
    change (∑ x : A × FrequencyTree A n × FrequencyTree A n,
      K x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) *
        frequencyTreeWeight K W n x.2.1 * frequencyTreeWeight K W n x.2.2) ≤ _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          (∑ a : A, K a (frequencyRoot n x) (frequencyRoot n y)) *
            frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.sum_mul]
      _ ≤ ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          C * frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hsum _ _) (hweight x)) (hweight y)
      _ = C * ((∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) *
          (∑ y : FrequencyTree A n, frequencyTreeWeight K W n y)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      _ ≤ C * ((C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n)) *
          (C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ih ih hsum0 hbound0) hC
      _ = _ := by
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
        have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have hnodes : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by omega
        rw [hnodes, hpow, pow_add, pow_add, pow_add, pow_one]
        ring

end Ostmann

end OAI
