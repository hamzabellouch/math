import OAI.Probability.ThorpShuffle.TaggedDeviation

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def freeOf {α : Type uα} [DecidableEq α] {k : ℕ} (e : Fin k → α) : α → Bool :=
  fun y => decide (∀ i, e i ≠ y)

@[simp] theorem freeOf_exposed {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (i : Fin k) : freeOf e (e i) = false := by
  simp [freeOf]

@[simp] theorem freeOf_true {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (y : α) : freeOf e y = true ↔ ∀ i, e i ≠ y := by
  simp [freeOf]

theorem freeOf_perm {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (g : Equiv.Perm α) (y : α) :
    freeOf (g ∘ e) y = freeOf e (g.symm y) := by
  simp [freeOf, ← g.eq_symm_apply]

theorem freeCount_perm {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (g : Equiv.Perm α) : freeCount (freeOf (g ∘ e)) = freeCount (freeOf e) := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  simp only [freeOf_perm]
  exact Equiv.sum_comp g.symm (fun x => if freeOf e x then (1 : ℝ) else 0)

theorem freeCount_freeOf {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (he : Function.Injective e) : freeCount (freeOf e) = Fintype.card α - k := by
  have hs : Finset.univ.filter (fun x => freeOf e x = true) = (Finset.univ.image e)ᶜ := by
    ext x
    simp [freeOf]
  unfold freeCount
  rw [hs, Finset.card_compl, Finset.card_image_of_injective _ he]
  simp

def completeTest {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (f : (Fin (k + 1) → α) → ℝ) (e : Fin k → α) : ℝ :=
  (1 / (freeCount (freeOf e) : ℝ)) * ∑ y, if freeOf e y then f (Fin.snoc e y) else 0

theorem completeTest_bound {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (f : (Fin (k + 1) → α) → ℝ) (hf : ∀ e, |f e| ≤ 1) (e : Fin k → α) :
    |completeTest f e| ≤ 1 := by
  unfold completeTest
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (freeCount (freeOf e) : ℝ))]
  have hs : |∑ y, if freeOf e y then f (Fin.snoc e y) else 0| ≤ freeCount (freeOf e) := by
    calc
      _ ≤ ∑ y, |if freeOf e y then f (Fin.snoc e y) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, if freeOf e y then (1 : ℝ) else 0 := Finset.sum_le_sum (fun y _ => by
        by_cases h : freeOf e y = true
        · simpa only [h, ↓reduceIte] using hf (Fin.snoc e y)
        · simp [h])
      _ = _ := sum_free_indicator _
  have hh := mul_le_mul_of_nonneg_left hs
    (by positivity : (0 : ℝ) ≤ 1 / (freeCount (freeOf e) : ℝ))
  by_cases hz : freeCount (freeOf e) = 0
  · simp [hz]
  · have hn : (freeCount (freeOf e) : ℝ) ≠ 0 := by exact_mod_cast hz
    simpa [hn] using hh

theorem uniform_tagged_completion {α : Type uα} [Fintype α] [DecidableEq α]
    {k : ℕ} (e : Fin k → α) (tag : α) (ht : freeOf e tag = true)
    (f : (Fin k → α) → α → ℝ) :
    mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) =
    mean (fun g : Equiv.Perm α => (1 / (freeCount (freeOf e) : ℝ)) *
      ∑ y, if freeOf (g ∘ e) y then f (g ∘ e) y else 0) := by
  have hm : (freeCount (freeOf e) : ℝ) ≠ 0 := by
    exact_mod_cast (freeCount_pos _ tag ht).ne'
  have hs (x : α) (hx : freeOf e x = true) :
      mean (fun g : Equiv.Perm α => f (g ∘ e) (g x)) =
        mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) := by
    have heq : (Equiv.swap tag x) ∘ e = e := by
      funext i
      exact Equiv.swap_apply_of_ne_of_ne ((freeOf_true e tag).mp ht i)
        ((freeOf_true e x).mp hx i)
    have h := mean_equiv (Equiv.mulRight (Equiv.swap tag x))
      (fun g : Equiv.Perm α => f (g ∘ e) (g tag))
    convert h using 1
    apply mean_congr
    intro g
    change f (g ∘ e) (g x) = f (g ∘ ((Equiv.swap tag x) ∘ e)) (g (Equiv.swap tag x tag))
    rw [heq, Equiv.swap_apply_left]
  symm
  calc
    _ = mean (fun g : Equiv.Perm α => (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, if freeOf e x then f (g ∘ e) (g x) else 0) := by
      apply mean_congr
      intro g
      congr 1
      simp only [freeOf_perm]
      exact (Equiv.sum_comp g (fun y => if freeOf e (g.symm y) then f (g ∘ e) y else 0)).symm.trans
        (by simp only [Equiv.symm_apply_apply])
    _ = (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, mean (fun g : Equiv.Perm α => if freeOf e x then f (g ∘ e) (g x) else 0) := by
      rw [mean_const_mul, mean_sum]
    _ = (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, if freeOf e x then mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      cases hx : freeOf e x
      · simp [mean_zero]
      · simpa only [hx, ↓reduceIte] using hs x hx
    _ = _ := by
      have hid (x : α) : (if freeOf e x then mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) else 0) =
          (if freeOf e x then (1 : ℝ) else 0) * mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) := by
        cases freeOf e x <;> simp
      simp_rw [hid]
      rw [← Finset.sum_mul, sum_free_indicator]
      field_simp

end Conditional

end Thorp

end

end OAI
