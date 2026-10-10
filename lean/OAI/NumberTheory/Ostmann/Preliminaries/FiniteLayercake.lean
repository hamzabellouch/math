import Mathlib.Order.Interval.Finset.Basic
import OAI.NumberTheory.Ostmann.Construction.MatchedHarmonicPrior

namespace OAI

/-! # A finite positive layer decomposition for the diagonal ratio -/

namespace Ostmann

open scoped BigOperators Classical

/-- Uniform bounds on all upper level sums control every nonnegative bounded
multiplier with no loss depending on the number of sampled values. -/
theorem finite_level_sum_norm_bound {A : Type*} (S : Finset A)
    (r : A → ℝ) (c : A → ℂ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hr : ∀ a ∈ S, 0 ≤ r a ∧ r a ≤ M)
    (hlevel : ∀ t : ℝ, 0 < t → ‖∑ a ∈ S, if t ≤ r a then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, (r a : ℂ) * c a‖ ≤ M * δ := by
  revert r M
  refine Finset.strongInductionOn S ?_
  intro S ih r M hM hr hlevel
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := S.exists_min_image r hS
    let m := r a
    have hm : 0 ≤ m := (hr a ha).1
    have hmM : m ≤ M := (hr a ha).2
    have herase : S.erase a ⊂ S := Finset.erase_ssubset ha
    have hr' : ∀ x ∈ S.erase a, 0 ≤ r x - m ∧ r x - m ≤ M - m := by
      intro x hx
      have hxS := Finset.mem_of_mem_erase hx
      exact ⟨sub_nonneg.mpr (hmin x hxS), sub_le_sub_right (hr x hxS).2 m⟩
    have hlevel' (t : ℝ) (ht : 0 < t) :
        ‖∑ x ∈ S.erase a, if t ≤ r x - m then c x else 0‖ ≤ δ := by
      have he : (∑ x ∈ S.erase a, if t ≤ r x - m then c x else 0) =
          ∑ x ∈ S, if t + m ≤ r x then c x else 0 := by
        rw [Finset.sum_erase_eq_sub ha]
        have heq (x : A) : (t ≤ r x - m) = (t + m ≤ r x) := propext (le_sub_iff_add_le)
        simp only [heq]
        have hno : ¬t + m ≤ r a := by dsimp [m]; linarith
        simp only [hno, ite_false, sub_zero]
      rw [he]
      exact hlevel (t + m) (add_pos_of_pos_of_nonneg ht hm)
    have hrest := ih (S.erase a) herase (fun x => r x - m) (M - m)
      (sub_nonneg.mpr hmM) hr' hlevel'
    have hfirst : ‖(m : ℂ) * ∑ x ∈ S, c x‖ ≤ m * δ := by
      by_cases hm0 : m = 0
      · simp only [hm0, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
      · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
        have he : (∑ x ∈ S, if m ≤ r x then c x else 0) = ∑ x ∈ S, c x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact ite_eq_left (hmin x hx)
        have hh := hlevel m hmp
        rw [he] at hh
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left hh hm
    have he : (∑ x ∈ S, (r x : ℂ) * c x) =
        (m : ℂ) * (∑ x ∈ S, c x) + ∑ x ∈ S.erase a, ((r x - m : ℝ) : ℂ) * c x := by
      rw [Finset.sum_erase_eq_sub ha]
      simp only [show r a - m = 0 from sub_self _, Complex.ofReal_zero, zero_mul, sub_zero,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      push_cast
      ring
    rw [he]
    calc
      _ ≤ ‖(m : ℂ) * ∑ x ∈ S, c x‖ + ‖∑ x ∈ S.erase a, ((r x - m : ℝ) : ℂ) * c x‖ := norm_add_le _ _
      _ ≤ m * δ + (M - m) * δ := add_le_add hfirst hrest
      _ = M * δ := by ring
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simpa only [Finset.sum_empty, norm_zero] using mul_nonneg hM hδ

/-- The normalized reciprocal product costs no additional constant once the
same correlation bound holds with arbitrary product upper cutoffs. -/
theorem finite_product_ratio_norm_bound {A : Type*} (S : Finset A)
    (H : A → ℝ) (c : A → ℂ) (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ)
    (hH : ∀ a ∈ S, X ≤ H a)
    (hcut : ∀ R : ℝ, ‖∑ a ∈ S, if H a ≤ R then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, ((X / H a : ℝ) : ℂ) * c a‖ ≤ δ := by
  have hp (a) (ha : a ∈ S) : 0 < H a := hX.trans_le (hH a ha)
  have hr : ∀ a ∈ S, 0 ≤ X / H a ∧ X / H a ≤ 1 := by
    intro a ha
    exact ⟨div_nonneg hX.le (hp a ha).le, (div_le_one (hp a ha)).mpr (hH a ha)⟩
  have hl (t : ℝ) (ht : 0 < t) :
      ‖∑ a ∈ S, if t ≤ X / H a then c a else 0‖ ≤ δ := by
    have he : (∑ a ∈ S, if t ≤ X / H a then c a else 0) =
        ∑ a ∈ S, if H a ≤ X / t then c a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hh : (t ≤ X / H a) = (H a ≤ X / t) := by
        apply propext
        rw [le_div_iff₀ (hp a ha), le_div_iff₀ ht, mul_comm t]
      simp only [hh]
    rw [he]
    exact hcut (X / t)
  simpa only [one_mul] using finite_level_sum_norm_bound S (fun a => X / H a) c 1 δ
    (by norm_num) hδ hr hl

/-- Zero coefficients can carry arbitrary product values. Only the original
supported terms need the lower product range. -/
theorem finite_product_ratio_norm_bound_on_support {A : Type*} (S : Finset A)
    (H : A → ℝ) (c : A → ℂ) (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ)
    (hsupport : ∀ a ∈ S, c a ≠ 0 → X ≤ H a)
    (hcut : ∀ R : ℝ, ‖∑ a ∈ S, if H a ≤ R then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, ((X / H a : ℝ) : ℂ) * c a‖ ≤ δ := by
  let S' := S.filter (fun a => X ≤ H a)
  have hz (a) (ha : a ∈ S) (hbad : ¬X ≤ H a) : c a = 0 := by
    by_contra hn
    exact hbad (hsupport a ha hn)
  have he (f : A → ℂ) : (∑ a ∈ S', f a * c a) = ∑ a ∈ S, f a * c a := by
    rw [show S' = S.filter (fun a => X ≤ H a) from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hh : X ≤ H a
    · simp only [hh, ite_true]
    · simp only [hh, ite_false, hz a ha hh, mul_zero]
  have hc (R : ℝ) : ‖∑ a ∈ S', if H a ≤ R then c a else 0‖ ≤ δ := by
    have he' : (∑ a ∈ S', if H a ≤ R then c a else 0) =
        ∑ a ∈ S, if H a ≤ R then c a else 0 := by
      simpa only [ite_mul, one_mul, zero_mul] using he (fun a => if H a ≤ R then 1 else 0)
    rw [he']
    exact hcut R
  rw [← he (fun a => ((X / H a : ℝ) : ℂ))]
  exact finite_product_ratio_norm_bound S' H c X δ hX hδ
    (fun _ ha => (Finset.mem_filter.mp ha).2) hc

end Ostmann

end OAI
