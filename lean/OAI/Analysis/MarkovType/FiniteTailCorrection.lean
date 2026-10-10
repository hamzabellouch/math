import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def finiteCoefficientTail {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, if j ≤ i then a i else 0

noncomputable def finiteTailLinear (n : ℕ) (j : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun a := finiteCoefficientTail a j
  map_add' a b := by
    change (∑ i, if j ≤ i then a i + b i else 0) =
      (∑ i, if j ≤ i then a i else 0) + ∑ i, if j ≤ i then b i else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hji : j ≤ i <;> simp only [hji, ite_true, ite_false, add_zero]
  map_smul' c a := by
    change (∑ i, if j ≤ i then c * a i else 0) =
      c * ∑ i, if j ≤ i then a i else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hji : j ≤ i <;> simp only [hji, ite_true, ite_false, mul_zero]

@[simp] theorem finiteTailLinear_apply (n : ℕ) (j : Fin n) (a : Fin n → ℝ) :
    finiteTailLinear n j a = finiteCoefficientTail a j := rfl

@[simp] theorem finiteTail_zero {n : ℕ} (j : Fin n) :
    finiteCoefficientTail (0 : Fin n → ℝ) j = 0 := by
  simp [finiteCoefficientTail]

theorem finiteTail_add {n : ℕ} (a b : Fin n → ℝ) (j : Fin n) :
    finiteCoefficientTail (a + b) j = finiteCoefficientTail a j + finiteCoefficientTail b j :=
  (finiteTailLinear n j).map_add a b

theorem finiteTail_sub {n : ℕ} (a b : Fin n → ℝ) (j : Fin n) :
    finiteCoefficientTail (a - b) j = finiteCoefficientTail a j - finiteCoefficientTail b j :=
  (finiteTailLinear n j).map_sub a b

@[simp] theorem finiteTail_single {n : ℕ} (i j : Fin n) (a : ℝ) :
    finiteCoefficientTail (Pi.single i a) j = if j ≤ i then a else 0 := by
  classical
  unfold finiteCoefficientTail
  calc
    (∑ k, if j ≤ k then (Pi.single i a : Fin n → ℝ) k else 0) =
        if j ≤ i then (Pi.single i a : Fin n → ℝ) i else 0 := by
      apply Fintype.sum_eq_single i
      intro k hki
      simp only [Pi.single_eq_of_ne hki, ite_self]
    _ = if j ≤ i then a else 0 := by rw [Pi.single_eq_same]

theorem finiteTail_sub_next {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hnext : i.val + 1 < n) :
    finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩ = a i := by
  classical
  unfold finiteCoefficientTail
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin n, ((if i ≤ j then a j else 0) -
        (if (⟨i.val + 1, hnext⟩ : Fin n) ≤ j then a j else 0))) =
        ∑ j : Fin n, if j = i then a j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        have hnot : ¬ (⟨i.val + 1, hnext⟩ : Fin n) ≤ i := by
          change ¬ i.val + 1 ≤ i.val
          omega
        simp only [le_refl, ite_true, hnot, ite_false, sub_zero]
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hle : (i ≤ j) ↔ ((⟨i.val + 1, hnext⟩ : Fin n) ≤ j) := by
          change (i.val ≤ j.val) ↔ (i.val + 1 ≤ j.val)
          omega
        simp only [hle, hji, ite_false, sub_self]
    _ = a i := by simp

theorem eq_finiteTail_sub_next {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hnext : i.val + 1 < n) :
    a i = finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩ :=
  (finiteTail_sub_next a i hnext).symm

theorem finiteTail_eq_of_last {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hlast : i.val + 1 = n) : finiteCoefficientTail a i = a i := by
  classical
  unfold finiteCoefficientTail
  calc
    (∑ j : Fin n, if i ≤ j then a j else 0) =
        ∑ j : Fin n, if j = i then a j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      have hle : (i ≤ j) ↔ j = i := by
        constructor
        · intro hij
          apply Fin.ext
          change i.val ≤ j.val at hij
          have hjn := j.isLt
          omega
        · intro hji
          subst j
          exact le_rfl
      simp only [hle]
    _ = a i := by simp

@[simp] theorem finiteTail_last {n : ℕ} (a : Fin (n + 1) → ℝ) :
    finiteCoefficientTail a (Fin.last n) = a (Fin.last n) :=
  finiteTail_eq_of_last a (Fin.last n) rfl

theorem abs_le_two_mul_of_finiteTail_le {n : ℕ} (a : Fin n → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ j, |finiteCoefficientTail a j| ≤ M) (i : Fin n) :
    |a i| ≤ 2 * M := by
  by_cases hnext : i.val + 1 < n
  · rw [eq_finiteTail_sub_next a i hnext]
    calc
      |finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩| ≤
          |finiteCoefficientTail a i| + |finiteCoefficientTail a ⟨i.val + 1, hnext⟩| := abs_sub _ _
      _ ≤ M + M := add_le_add (h i) (h ⟨i.val + 1, hnext⟩)
      _ = 2 * M := by ring
  · have hlast : i.val + 1 = n := by
      have hin := i.isLt
      omega
    have hi : |a i| ≤ M := by
      rw [← finiteTail_eq_of_last a i hlast]
      exact h i
    linarith

theorem sum_abs_le_two_mul_card_mul_of_finiteTail_le {n : ℕ}
    (a : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j, |finiteCoefficientTail a j| ≤ M) :
    (∑ i, |a i|) ≤ 2 * (n : ℝ) * M := by
  calc
    (∑ i, |a i|) ≤ ∑ _i : Fin n, 2 * M := by
      exact Finset.sum_le_sum (fun i _ => abs_le_two_mul_of_finiteTail_le a hM h i)
    _ = 2 * (n : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem eq_zero_of_finiteTail_eq_zero {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ j, finiteCoefficientTail a j = 0) : a = 0 := by
  have hbound : ∀ j, |finiteCoefficientTail a j| ≤ (0 : ℝ) := by
    intro j
    simpa only [h j, abs_zero] using (le_refl (0 : ℝ))
  funext i
  have hi := abs_le_two_mul_of_finiteTail_le a (le_refl 0) hbound i
  have habs : |a i| = 0 := le_antisymm (by simpa only [mul_zero] using hi) (abs_nonneg _)
  exact abs_eq_zero.mp habs

theorem exists_finiteTail_abs_max {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) :
    ∃ j : Fin n, ∀ i : Fin n, |finiteCoefficientTail a i| ≤ |finiteCoefficientTail a j| := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => |finiteCoefficientTail a i|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩

theorem exists_finiteTail_max_bound {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j, |finiteCoefficientTail a j| ≤ M) ∧
      (∃ j, |finiteCoefficientTail a j| = M) ∧ (∑ i, |a i|) ≤ 2 * (n : ℝ) * M := by
  obtain ⟨j, hj⟩ := exists_finiteTail_abs_max a hn
  refine ⟨|finiteCoefficientTail a j|, abs_nonneg _, hj, ⟨j, rfl⟩, ?_⟩
  exact sum_abs_le_two_mul_card_mul_of_finiteTail_le a (abs_nonneg _) hj

theorem finiteTail_le_two_norm_of_approx {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] X) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : 2 * (n : ℝ) * η ≤ (1 / 2 : ℝ))
    (happrox : ∀ (a : Fin n → ℝ) (j : Fin n),
      |finiteCoefficientTail a j| ≤ ‖A a‖ + η * ∑ i, |a i|) :
    ∀ (a : Fin n → ℝ) (j : Fin n), |finiteCoefficientTail a j| ≤ 2 * ‖A a‖ := by
  intro a j
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  obtain ⟨jmax, hmax⟩ := exists_finiteTail_abs_max a hn
  have hM : 0 ≤ |finiteCoefficientTail a jmax| := abs_nonneg _
  have hsum := sum_abs_le_two_mul_card_mul_of_finiteTail_le a hM hmax
  have herror : η * (∑ i, |a i|) ≤ (1 / 2 : ℝ) * |finiteCoefficientTail a jmax| := by
    calc
      η * (∑ i, |a i|) ≤ η * (2 * (n : ℝ) * |finiteCoefficientTail a jmax|) :=
        mul_le_mul_of_nonneg_left hsum hη
      _ = (2 * (n : ℝ) * η) * |finiteCoefficientTail a jmax| := by ring
      _ ≤ (1 / 2 : ℝ) * |finiteCoefficientTail a jmax| :=
        mul_le_mul_of_nonneg_right hsmall hM
  have hmaxnorm : |finiteCoefficientTail a jmax| ≤ 2 * ‖A a‖ := by
    have hpair := happrox a jmax
    linarith
  exact (hmax j).trans hmaxnorm

end MarkovSuperreflexivity

end OAI
