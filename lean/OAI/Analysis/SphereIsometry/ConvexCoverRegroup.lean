import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Regrouping a convex hull over a finite cover

For a finite family of nonempty sets, every point in the convex hull of their
union is a convex combination with one point from each individual convex hull.
The proof establishes convexity of the represented set. Zero coefficients are
handled by choosing points inside the corresponding sets, without assuming
that those sets contain the origin.
-/

namespace Tingley

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Points represented by probability weights and one point in each member of
a finite family of sets. Membership is required even at zero-weight indices. -/
def finiteMixtures (B : ι → Set E) : Set E :=
  {x | ∃ (w : ι → ℝ) (z : ι → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    (∀ i, z i ∈ B i) ∧ (∑ i, w i • z i) = x}

/-- Mixing probability-weighted representations preserves representation when
each coordinate set is convex. No nonemptiness premise is needed here. -/
theorem convex_finiteMixtures (B : ι → Set E) (hB : ∀ i, Convex ℝ (B i)) :
    Convex ℝ (finiteMixtures B) := by
  classical
  rintro x ⟨wx, zx, hwx, hwxsum, hzx, hx⟩
    y ⟨wy, zy, hwy, hwysum, hzy, hy⟩ a b ha hb hab
  have hex (i : ι) :
      ∃ u ∈ B i, (a * wx i + b * wy i) • u =
        (a * wx i) • zx i + (b * wy i) • zy i :=
    (hB i).exists_mem_add_smul_eq (hzx i) (hzy i)
      (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  choose u hu hueq using hex
  refine ⟨fun i => a * wx i + b * wy i, u, ?_, ?_, hu, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  · calc
      (∑ i, (a * wx i + b * wy i)) =
          a * (∑ i, wx i) + b * (∑ i, wy i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 := by simp only [hwxsum, hwysum, mul_one, hab]
  · calc
      (∑ i, (a * wx i + b * wy i) • u i) =
          ∑ i, ((a * wx i) • zx i + (b * wy i) • zy i) :=
        Finset.sum_congr rfl fun i _ => hueq i
      _ = a • (∑ i, wx i • zx i) + b • (∑ i, wy i • zy i) := by
        simp only [Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
      _ = a • x + b • y := by rw [hx, hy]

/-- Regroup a point of a convex hull along an arbitrary finite cover by
nonempty sets. Cover members may be infinite, overlapping, or nonclosed. -/
theorem convexHull_cover_representation
    (H : Set E) (A : ι → Set E)
    (hne : ∀ i, (A i).Nonempty)
    (hcover : ∀ x ∈ H, ∃ i, x ∈ A i)
    {x : E} (hx : x ∈ convexHull ℝ H) :
    ∃ (w : ι → ℝ) (z : ι → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, z i ∈ convexHull ℝ (A i)) ∧
      (∑ i, w i • z i) = x := by
  classical
  choose base hbase using hne
  have hcontains : H ⊆ finiteMixtures (fun i => convexHull ℝ (A i)) := by
    intro y hy
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨fun i => if i = j then 1 else 0,
      fun i => if i = j then y else base i, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j <;> simp [hij]
    · simp
    · intro i
      by_cases hij : i = j
      · subst i
        simpa only [ite_eq_left rfl, ite_true] using subset_convexHull ℝ (A j) hj
      · simpa only [ite_eq_right hij] using subset_convexHull ℝ (A i) (hbase i)
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp
      · intro i _ hij
        simp [hij]
  exact convexHull_min hcontains
    (convex_finiteMixtures _ fun i => convex_convexHull ℝ (A i)) hx

end Tingley

end OAI
