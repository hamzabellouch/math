import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section

universe uα uι uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

def realAvg (A : Finset α) (f : α → ℝ) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ x ∈ A, f x

theorem realAvg_eq_sum_div (A : Finset α) (f : α → ℝ) :
    realAvg A f = (∑ x ∈ A, f x) / (A.card : ℝ) := by
  simp only [realAvg, div_eq_mul_inv, mul_comm]

theorem realAvg_congr (A : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ A, f x = g x) : realAvg A f = realAvg A g := by
  unfold realAvg
  rw [Finset.sum_congr rfl hfg]

@[simp] theorem realAvg_zero (A : Finset α) : realAvg A (fun _ => 0) = 0 := by
  simp [realAvg]

theorem realAvg_add (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x + g x) = realAvg A f + realAvg A g := by
  simp only [realAvg, Finset.sum_add_distrib, mul_add]

theorem realAvg_sub (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x - g x) = realAvg A f - realAvg A g := by
  simp only [realAvg, Finset.sum_sub_distrib, mul_sub]

theorem realAvg_neg (A : Finset α) (f : α → ℝ) :
    realAvg A (fun x => -f x) = -realAvg A f := by
  simp only [realAvg, Finset.sum_neg_distrib, mul_neg]

theorem realAvg_const_mul (A : Finset α) (c : ℝ) (f : α → ℝ) :
    realAvg A (fun x => c * f x) = c * realAvg A f := by
  simp only [realAvg, ← Finset.mul_sum, mul_left_comm]

theorem realAvg_mul_const (A : Finset α) (f : α → ℝ) (c : ℝ) :
    realAvg A (fun x => f x * c) = realAvg A f * c := by
  simp only [realAvg, ← Finset.sum_mul, mul_assoc]

theorem realAvg_sum (A : Finset α) (B : Finset ι) (f : ι → α → ℝ) :
    realAvg A (fun x => ∑ i ∈ B, f i x) = ∑ i ∈ B, realAvg A (f i) := by
  unfold realAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem realAvg_sum_univ [Fintype ι] (A : Finset α) (f : ι → α → ℝ) :
    realAvg A (fun x => ∑ i, f i x) = ∑ i, realAvg A (f i) :=
  realAvg_sum A Finset.univ f

theorem realAvg_mono (A : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ A, f x ≤ g x) : realAvg A f ≤ realAvg A g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card))

theorem realAvg_nonneg (A : Finset α) {f : α → ℝ}
    (hf : ∀ x ∈ A, 0 ≤ f x) : 0 ≤ realAvg A f := by
  simpa only [realAvg_zero] using realAvg_mono A hf

theorem realAvg_const (A : Finset α) (hA : A.Nonempty) (c : ℝ) :
    realAvg A (fun _ => c) = c := by
  have hc : (A.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hA))
  simp [realAvg, nsmul_eq_mul, hc]

theorem realAvg_le_const (A : Finset α) (hA : A.Nonempty) {f : α → ℝ} {c : ℝ}
    (hf : ∀ x ∈ A, f x ≤ c) : realAvg A f ≤ c := by
  simpa only [realAvg_const A hA c] using realAvg_mono A hf

theorem const_le_realAvg (A : Finset α) (hA : A.Nonempty) {f : α → ℝ} {c : ℝ}
    (hf : ∀ x ∈ A, c ≤ f x) : c ≤ realAvg A f := by
  simpa only [realAvg_const A hA c] using realAvg_mono A hf

theorem abs_realAvg_le (A : Finset α) (f : α → ℝ) :
    |realAvg A f| ≤ realAvg A (fun x => |f x|) := by
  unfold realAvg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg A.card))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs f A)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card))

theorem realAvg_abs_le_one (A : Finset α) (hA : A.Nonempty) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : |realAvg A f| ≤ 1 :=
  (abs_realAvg_le A f).trans (realAvg_le_const A hA (fun x _ => hf x))

section Cancellation

variable [DecidableEq α]

/-- The exact common-intersection cancellation, before any estimate. -/
theorem sum_sub_eq_sdiff_sub (U V : Finset α) (f : α → ℝ) :
    (∑ x ∈ U, f x) - ∑ x ∈ V, f x =
      (∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x :=
  (Finset.sum_sdiff_sub_sum_sdiff (s₁ := V) (s₂ := U) (f := f)).symm

theorem card_symmDiff_eq_sdiff_add (U V : Finset α) :
    (U ∆ V).card = (U \ V).card + (V \ U).card := by
  change ((U \ V) ∪ (V \ U)).card = _
  exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff

omit [DecidableEq α] in
theorem abs_sum_le_card [DecidableEq α] (A : Finset α) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |∑ x ∈ A, f x| ≤ (A.card : ℝ) := by
  calc
    |∑ x ∈ A, f x| ≤ ∑ x ∈ A, |f x| := Finset.abs_sum_le_sum_abs f A
    _ ≤ ∑ _x ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = (A.card : ℝ) := by simp

/-- The full symmetric difference counts both residual pieces exactly once. -/
theorem abs_sum_sub_le_card_symmDiff (U V : Finset α) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x ∈ U, f x) - ∑ x ∈ V, f x| ≤ ((U ∆ V).card : ℝ) := by
  rw [sum_sub_eq_sdiff_sub]
  calc
    |(∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x| ≤
        |∑ x ∈ U \ V, f x| + |∑ x ∈ V \ U, f x| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ x ∈ U \ V, f x) (-(∑ x ∈ V \ U, f x))
    _ ≤ ((U \ V).card : ℝ) + ((V \ U).card : ℝ) :=
      add_le_add (abs_sum_le_card (U \ V) f hf) (abs_sum_le_card (V \ U) f hf)
    _ = ((U ∆ V).card : ℝ) := by rw [card_symmDiff_eq_sdiff_add, Nat.cast_add]

end Cancellation

section Translation

variable {G : Type uG} [Group G] [DecidableEq G]

def leftTranslate (h : G) (A : Finset G) : Finset G := A.image (fun g => h * g)

def boundaryRatio (A : Finset G) (h : G) : ℝ :=
  ((leftTranslate h A ∆ A).card : ℝ) / (A.card : ℝ)

theorem sum_leftTranslate (h : G) (A : Finset G) (f : G → ℝ) :
    (∑ g ∈ A, f (h * g)) = ∑ x ∈ leftTranslate h A, f x := by
  unfold leftTranslate
  exact (Finset.sum_image (fun _ _ _ _ hxy => mul_left_cancel hxy)).symm

@[simp] theorem card_leftTranslate (h : G) (A : Finset G) :
    (leftTranslate h A).card = A.card :=
  Finset.card_image_of_injective A (fun _ _ hxy => mul_left_cancel hxy)

theorem boundaryRatio_nonneg (A : Finset G) (h : G) : 0 ≤ boundaryRatio A h :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem abs_sum_translate_sub_le (A : Finset G) (h : G) (f : G → ℝ)
    (hf : ∀ g, |f g| ≤ 1) :
    |(∑ g ∈ A, f (h * g)) - ∑ g ∈ A, f g| ≤
      ((leftTranslate h A ∆ A).card : ℝ) := by
  rw [sum_leftTranslate]
  exact abs_sum_sub_le_card_symmDiff (leftTranslate h A) A f hf

/-- The finite-translation inequality for every globally unit-bounded function. -/
theorem abs_realAvg_translate_sub_le (A : Finset G) (hA : A.Nonempty)
    (h : G) (f : G → ℝ) (hf : ∀ g, |f g| ≤ 1) :
    |realAvg A (fun g => f (h * g)) - realAvg A f| ≤ boundaryRatio A h := by
  have hc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  rw [realAvg_eq_sum_div, realAvg_eq_sum_div, ← sub_div, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (abs_sum_translate_sub_le A h f hf) hc.le

/-- The real maximum requires an actual member of the fixed transport set. -/
def boundaryMax (S : Finset G) (hS : S.Nonempty) (A : Finset G) : ℝ := by
  classical
  exact (S.image (boundaryRatio A)).max' (hS.image _)

theorem boundaryMax_attained (S : Finset G) (hS : S.Nonempty) (A : Finset G) :
    ∃ h ∈ S, boundaryRatio A h = boundaryMax S hS A := by
  classical
  have hm : boundaryMax S hS A ∈ S.image (boundaryRatio A) :=
    Finset.max'_mem _ _
  exact Finset.mem_image.mp hm

theorem boundaryRatio_le_max (S : Finset G) (hS : S.Nonempty) (A : Finset G)
    {h : G} (hh : h ∈ S) : boundaryRatio A h ≤ boundaryMax S hS A := by
  classical
  exact (S.image (boundaryRatio A)).le_max' (boundaryRatio A h)
    (Finset.mem_image_of_mem _ hh)

theorem boundaryMax_nonneg (S : Finset G) (hS : S.Nonempty) (A : Finset G) :
    0 ≤ boundaryMax S hS A := by
  obtain ⟨h, _, hh⟩ := boundaryMax_attained S hS A
  rw [← hh]
  exact boundaryRatio_nonneg A h

theorem exists_boundary_ge_of_le_max (S : Finset G) (hS : S.Nonempty)
    (A : Finset G) {b : ℝ} (hb : b ≤ boundaryMax S hS A) :
    ∃ h ∈ S, b ≤ boundaryRatio A h := by
  obtain ⟨h, hh, hmax⟩ := boundaryMax_attained S hS A
  exact ⟨h, hh, hmax.symm ▸ hb⟩

end Translation

end ThompsonNonamenability

end

end OAI
