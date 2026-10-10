import OAI.Combinatorics.ExpectationThreshold.SelectorTruncationDefinitions
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The right-hand slope at a maximal admissible cutoff

A finite minimum provides an actual larger cutoff below every currently
heavy weight.  Between these cutoffs the truncated excess has the exact
affine increment contributed by the heavy coordinates.  Weights equal to
the original cutoff remain saturated, including when the cutoff is zero.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- There is a strictly larger cutoff, at most one, that does not pass any
weight strictly above the current cutoff. -/
theorem exists_short_right_cutoff (w : α → ℝ) {ε : ℝ} (hε : ε < 1) :
    ∃ u : ℝ, ε < u ∧ u ≤ 1 ∧ ∀ x, ε < w x → u ≤ w x := by
  classical
  let S : Finset ℝ := insert 1 ((heavySet w ε).image w)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, S.min'_le 1 (Finset.mem_insert_self _ _), ?_⟩
  · apply (Finset.lt_min'_iff S hS).2
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hε
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact mem_heavySet.mp hx
  · intro x hx
    apply S.min'_le (w x)
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, mem_heavySet.mpr hx, rfl⟩)

/-- On the first interval to the right of a cutoff, precisely the strictly
heavy coordinates vary.  The inclusion in `A` makes their coefficient `d`. -/
theorem truncatedExcess_sub_eq_heavy_increment (w : α → ℝ) (A : Finset α)
    (d ε u : ℝ) (hεu : ε ≤ u)
    (hupper : ∀ x, ε < w x → u ≤ w x)
    (hheavy : ∀ x, ε < w x → x ∈ A) :
    truncatedExcess w A d u - truncatedExcess w A d ε =
      (u - ε) * d * ((heavySet w ε).card : ℝ) := by
  classical
  calc
    truncatedExcess w A d u - truncatedExcess w A d ε =
        ∑ x, if ε < w x then (u - ε) * d else 0 := by
      unfold truncatedExcess
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ε < w x
      · simp only [min_eq_right (hupper x hx), min_eq_right hx.le,
          ite_eq_left hx, ite_eq_left (hheavy x hx)]
        ring
      · have hxε : w x ≤ ε := le_of_not_gt hx
        simp only [min_eq_left (hxε.trans hεu), min_eq_left hxε,
          ite_eq_right hx, sub_self]
    _ = ∑ x ∈ heavySet w ε, (u - ε) * d := by
      rw [← Finset.sum_filter]
      rfl
    _ = (u - ε) * d * ((heavySet w ε).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The cardinality conclusion of maximal truncation.  Existence of a
maximal admissible cutoff is supplied separately by compactness. -/
theorem maximal_admissible_card_bound (w : α → ℝ) (A : Finset α) (m d ε : ℝ)
    (hwnonneg : ∀ x, 0 ≤ w x) (hwsum : ∑ x, w x = 1)
    (hm0 : 0 ≤ m) (_hd0 : 0 < d) (_hd1 : d < 1)
    (hε : Admissible w A m d ε)
    (hmax : ∀ u : ℝ, Admissible w A m d u → u ≤ ε) :
    d * ((heavySet w ε).card : ℝ) ≤ m := by
  classical
  have hwle (x : α) : w x ≤ 1 := by
    calc
      w x ≤ ∑ y, w y :=
        Finset.single_le_sum (fun y _ => hwnonneg y) (Finset.mem_univ x)
      _ = 1 := hwsum
  by_cases hεone : ε = 1
  · have hempty : heavySet w ε = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hlt := mem_heavySet.mp hx
      rw [hεone] at hlt
      exact (not_lt_of_ge (hwle x)) hlt
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero] using hm0
  · have hεlt : ε < 1 := lt_of_le_of_ne hε.2.1 hεone
    obtain ⟨u, hεu, hu1, hupper⟩ := exists_short_right_cutoff w hεlt
    by_contra hbound
    have hgap : m < d * ((heavySet w ε).card : ℝ) := lt_of_not_ge hbound
    have haffine := truncatedExcess_sub_eq_heavy_increment w A d ε u
      hεu.le hupper hε.2.2.1
    have hslope : 0 ≤ (u - ε) * (d * ((heavySet w ε).card : ℝ) - m) :=
      mul_nonneg (sub_nonneg.mpr hεu.le) (sub_nonneg.mpr hgap.le)
    have htest : m * u ≤ truncatedExcess w A d u := by
      have htestε := hε.2.2.2
      nlinarith
    have hu : Admissible w A m d u :=
      ⟨hε.1.trans hεu.le, hu1,
        fun x hx => hε.2.2.1 x (hεu.trans hx), htest⟩
    exact (not_lt_of_ge (hmax u hu)) hεu

end TalagrandThreshold.Selector

end OAI
