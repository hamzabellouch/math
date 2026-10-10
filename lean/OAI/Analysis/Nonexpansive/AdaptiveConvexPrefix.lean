import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-!
# Finite convex witnesses for adaptive anchors

Closure of a convex hull is approximated by actual finite convex combinations.
For a sequence, the coefficients can be extended by zero to a whole initial
segment. Removing zero coefficients then preserves their original order.
-/

open scoped BigOperators
open Set

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A point of a closed convex hull admits a convex approximation indexed by a
nonempty `Fin` type. The points belong to the original set. -/
theorem closure_convexHull_exists_fin {D : Set X} {x : X}
    (hx : x ∈ closure (convexHull ℝ D)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (q : ℕ), 0 < q ∧ ∃ (d : Fin q → X) (w : Fin q → ℝ),
      (∀ i, d i ∈ D) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ‖(∑ i, w i • d i) - x‖ < τ := by
  classical
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx τ hτ
  obtain ⟨ι, hι, w, z, hw, hw1, hz, hzy⟩ :=
    mem_convexHull_iff_exists_fintype.mp hy
  let : Fintype ι := hι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hm : (∑ i : Fin (Fintype.card ι), w (e i)) = 1 := by
    rw [e.sum_comp, hw1]
  have hq : 0 < Fintype.card ι := by
    by_contra h
    have hzero : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    have : (0 : ℝ) = 1 := by simpa only [Fintype.sum_empty] using hw1
    exact zero_ne_one this
  refine ⟨Fintype.card ι, hq, z ∘ e, w ∘ e, fun i => hz (e i),
    fun i => hw (e i), hm, ?_⟩
  have hv : (∑ i : Fin (Fintype.card ι), w (e i) • z (e i)) = y := by
    exact (e.sum_comp (fun i => w i • z i)).trans hzy
  change ‖(∑ i : Fin (Fintype.card ι), w (e i) • z (e i)) - x‖ < τ
  rw [hv]
  simpa only [dist_eq_norm, norm_sub_rev] using hxy

/-- Extending a finitely supported sum by zero to a natural-number prefix
does not change it. -/
theorem sum_prefix_zero_extension {A : Type*} [AddCommMonoid A]
    (s : Finset ℕ) (f : ℕ → A) :
    (∑ i : Fin (s.sup id + 1), if (i : ℕ) ∈ s then f i else 0) =
      ∑ i ∈ s, f i := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ s then f i else 0) (s.sup id + 1)]
  symm
  calc
    (∑ i ∈ s, f i) = ∑ i ∈ s, if i ∈ s then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ite_eq_left hi]
    _ = ∑ i ∈ Finset.range (s.sup id + 1), if i ∈ s then f i else 0 := by
      apply Finset.sum_subset (Finset.subset_range_sup_succ s)
      intro i _ hi
      simp only [ite_eq_right hi]

/-- A convex approximation from a sequence uses coefficients on an entire
finite prefix; missing indices receive zero weight. -/
theorem closure_convexHull_range_exists_prefix (u : ℕ → X) {x : X}
    (hx : x ∈ closure (convexHull ℝ (range u))) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (N : ℕ), 0 < N ∧ ∃ (β : Fin N → ℝ),
      (∀ i, 0 ≤ β i) ∧ (∑ i, β i = 1) ∧
      ‖(∑ i, β i • u i) - x‖ < τ := by
  classical
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx τ hτ
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, w, hw, hw1, hwy⟩ := hy
  let N := s.sup id + 1
  let β : Fin N → ℝ := fun i => if (i : ℕ) ∈ s then w i else 0
  have hm : (∑ i : Fin N, β i) = 1 := by
    exact (sum_prefix_zero_extension s w).trans hw1
  have hv : (∑ i : Fin N, β i • u i) = y := by
    calc
      (∑ i : Fin N, β i • u i) =
          ∑ i : Fin N, if (i : ℕ) ∈ s then w i • u i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [β, ite_smul, zero_smul]
      _ = ∑ i ∈ s, w i • u i := sum_prefix_zero_extension s (fun i => w i • u i)
      _ = y := by
        rw [← s.affineCombination_eq_linear_combination u w hw1]
        exact hwy
  refine ⟨N, Nat.succ_pos _, β, ?_, hm, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) ∈ s
    · simpa only [β, ite_eq_left hi] using hw i hi
    · simp only [β, ite_eq_right hi, le_refl]
  · rw [hv]
    simpa only [dist_eq_norm, norm_sub_rev] using hxy

/-- Enumerating a finite subset in increasing order preserves every sum. -/
theorem sum_ordered_finset {N : ℕ} {A : Type*} [AddCommMonoid A]
    (s : Finset (Fin N)) (f : Fin N → A) :
    (∑ j : Fin s.card, f (s.orderEmbOfFin rfl j)) = ∑ i ∈ s, f i := by
  classical
  exact ((s.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : s => f i)).trans
    (Finset.sum_coe_sort s f)

/-- Remove exactly the zero coefficients of a finite convex combination.
The order embedding retains the original prefix order and index bounds. -/
theorem positive_support_reindex {N : ℕ} (u : Fin N → X) (β : Fin N → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hβ1 : ∑ i, β i = 1) :
    ∃ (q : ℕ), 0 < q ∧ ∃ (e : Fin q ↪o Fin N),
      (∀ j, 0 < β (e j)) ∧ (∑ j, β (e j) = 1) ∧
      (∑ j, β (e j) • u (e j)) = ∑ i, β i • u i := by
  classical
  let s := Finset.univ.filter (fun i => 0 < β i)
  have hz (i : Fin N) (hi : i ∉ s) : β i = 0 := by
    have hn : ¬ 0 < β i := by simpa only [s, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    exact le_antisymm (le_of_not_gt hn) (hβ i)
  have hm : (∑ i ∈ s, β i) = 1 := by
    calc
      (∑ i ∈ s, β i) = ∑ i, β i :=
        Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)
      _ = 1 := hβ1
  have hq : 0 < s.card := by
    apply Finset.card_pos.mpr
    by_contra h
    have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : (0 : ℝ) = 1 := by simpa only [hs, Finset.sum_empty] using hm
    exact zero_ne_one this
  refine ⟨s.card, hq, s.orderEmbOfFin rfl, ?_, ?_, ?_⟩
  · intro j
    exact (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl j)).2
  · exact (sum_ordered_finset s β).trans hm
  · exact (sum_ordered_finset s (fun i => β i • u i)).trans
      (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hz i hi, zero_smul]))

end ReflexiveFixedPoints

end OAI
