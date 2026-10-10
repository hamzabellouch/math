import OAI.Analysis.SphereIsometry.Supports
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# Positive combinations in a common support face

A norm-bounded functional that is one on a strictly positive barycenter is
one on every vertex. The resulting simultaneous support keeps the enlarged
convex hull in the unit sphere. For an infinite sequence, finite-prefix hull
containment passes to a closed ambient set without choosing a common support
for the entire sequence.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

section Scalar

variable {ι : Type*} [Fintype ι]

theorem eq_one_of_positive_weighted_sum (weights b : ι → ℝ)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hb : ∀ i, b i ≤ 1) (hsaturated : ∑ i, weights i * b i = 1) :
    ∀ i, b i = 1 := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ weights i * (1 - b i) :=
    fun i _ => mul_nonneg (hpos i).le (sub_nonneg.mpr (hb i))
  have hzero : ∑ i, weights i * (1 - b i) = 0 := by
    calc
      _ = (∑ i, weights i) - ∑ i, weights i * b i := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum, hsaturated, sub_self]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i
    (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hpos i)))).symm

end Scalar

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section FiniteCombination

variable {ι : Type*} [Fintype ι]

theorem support_eq_one_of_positive_sum (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (ha : φ (∑ i, weights i • v i) = 1) :
    ∀ i, φ (v i) = 1 := by
  apply eq_one_of_positive_weighted_sum weights (fun i => φ (v i)) hpos hsum
  · exact fun i => (apply_le_norm hφ (v i)).trans (hv i)
  · simpa only [map_sum, map_smul, smul_eq_mul] using ha

theorem SupportAt.eq_one_of_positive_sum {φ : X →L[ℝ] ℝ}
    (weights : ι → ℝ) (v : ι → X)
    (hφ : SupportAt φ (∑ i, weights i • v i))
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (ha : ‖∑ i, weights i • v i‖ = 1) :
    ∀ i, φ (v i) = 1 :=
  support_eq_one_of_positive_sum φ hφ.1 weights v hpos hsum hv (hφ.2.trans ha)

end FiniteCombination

/-- The closed unit ball cut by the level-one hyperplane of one functional. -/
def supportFace (φ : X →L[ℝ] ℝ) : Set X :=
  {x | ‖x‖ ≤ 1 ∧ φ x = 1}

theorem convex_supportFace (φ : X →L[ℝ] ℝ) : Convex ℝ (supportFace φ) := by
  rintro x ⟨hx, hφx⟩ y ⟨hy, hφy⟩ a b ha hb hab
  constructor
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa only [mul_one] using hab
  · simpa only [map_add, map_smul, smul_eq_mul, hφx, hφy, mul_one] using hab

theorem isClosed_supportFace (φ : X →L[ℝ] ℝ) : IsClosed (supportFace φ) :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_eq φ.continuous continuous_const)

theorem supportFace_subset_sphere (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    supportFace φ ⊆ {x : X | ‖x‖ = 1} := by
  intro x hx
  exact le_antisymm hx.1 (hx.2 ▸ apply_le_norm hφ x)

theorem convexHull_subset_supportFace (φ : X →L[ℝ] ℝ)
    {S : Set X} (hS : S ⊆ supportFace φ) :
    convexHull ℝ S ⊆ supportFace φ :=
  convexHull_min hS (convex_supportFace φ)

theorem closure_convexHull_subset_supportFace (φ : X →L[ℝ] ℝ)
    {S : Set X} (hS : S ⊆ supportFace φ) :
    closure (convexHull ℝ S) ⊆ supportFace φ :=
  closure_minimal (convexHull_subset_supportFace φ hS) (isClosed_supportFace φ)

section Enlargement

variable {ι : Type*} [Fintype ι]

theorem enlarged_convexHull_in_supportFace (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1) :
    convexHull ℝ (insert w (Set.range v)) ⊆ {x : X | ‖x‖ = 1 ∧ φ x = 1} := by
  have hall := support_eq_one_of_positive_sum φ hφ weights v hpos hsum
    (fun i => (hv i).le) ha
  have hvertices : insert w (Set.range v) ⊆ supportFace φ := by
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨hw.le, hwφ⟩
    · exact ⟨(hv i).le, hall i⟩
  intro x hx
  have hxface := convexHull_subset_supportFace φ hvertices hx
  exact ⟨supportFace_subset_sphere φ hφ hxface, hxface.2⟩

/-- The actual geometric propagation rule can now be applied to every new hull point. -/
theorem convexHull_insert_subset_of_common_support (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X) (E : Set X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1)
    (hprop : ∀ x, ‖x‖ = 1 → φ x = 1 → x ∈ E) :
    convexHull ℝ (insert w (Set.range v)) ⊆ E := by
  intro x hx
  have h := enlarged_convexHull_in_supportFace φ hφ weights v w hpos hsum hv hw ha hwφ hx
  exact hprop x h.1 h.2

end Enlargement

/-- The actual values at indices zero through n; repeated values are allowed. -/
def prefixVertices (v : ℕ → X) (n : ℕ) : Set X := v '' {i : ℕ | i ≤ n}

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem prefixVertices_mono (v : ℕ → X) : Monotone (prefixVertices v) := by
  intro n m hnm x hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, hi.trans hnm, rfl⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem prefixVertices_subset_range (v : ℕ → X) (n : ℕ) :
    prefixVertices v n ⊆ Set.range v := by
  rintro x ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem prefixVertices_eq_range_fin (v : ℕ → X) (n : ℕ) :
    prefixVertices v n = Set.range (fun i : Fin (n + 1) => v i.val) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, rfl⟩

theorem convexHull_range_eq_iUnion_prefix (v : ℕ → X) :
    convexHull ℝ (Set.range v) = ⋃ n, convexHull ℝ (prefixVertices v n) := by
  have hmono : Monotone (fun n => convexHull ℝ (prefixVertices v n)) :=
    fun _ _ hnm => convexHull_mono (prefixVertices_mono v hnm)
  have hdir : Directed (· ⊆ ·) (fun n => convexHull ℝ (prefixVertices v n)) :=
    fun n m => ⟨max n m, hmono (le_max_left n m), hmono (le_max_right n m)⟩
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨i, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i,
        subset_convexHull ℝ (prefixVertices v i) ⟨i, (by change i ≤ i; exact le_rfl), rfl⟩⟩
    · exact hdir.convex_iUnion (fun {n} => convex_convexHull ℝ (prefixVertices v n))
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact convexHull_mono (prefixVertices_subset_range v n) hn

theorem closure_convexHull_range_subset_of_prefix (v : ℕ → X)
    {E : Set X} (hE : IsClosed E)
    (hprefix : ∀ n, convexHull ℝ (prefixVertices v n) ⊆ E) :
    closure (convexHull ℝ (Set.range v)) ⊆ E := by
  apply closure_minimal _ hE
  rw [convexHull_range_eq_iUnion_prefix]
  exact Set.iUnion_subset hprefix

theorem closed_convex_extremal_hull (v : ℕ → X)
    {E : Set X} (hE : IsClosed E) (hEsphere : E ⊆ {x : X | ‖x‖ = 1})
    (hprefix : ∀ n, convexHull ℝ (prefixVertices v n) ⊆ E) :
    (closure (convexHull ℝ (Set.range v))).Nonempty ∧
    IsClosed (closure (convexHull ℝ (Set.range v))) ∧
    Convex ℝ (closure (convexHull ℝ (Set.range v))) ∧
    Bornology.IsBounded (closure (convexHull ℝ (Set.range v))) ∧
    closure (convexHull ℝ (Set.range v)) ⊆ E := by
  have hsub := closure_convexHull_range_subset_of_prefix v hE hprefix
  refine ⟨⟨v 0, subset_closure (subset_convexHull ℝ (Set.range v) ⟨0, rfl⟩)⟩,
    isClosed_closure, (convex_convexHull ℝ (Set.range v)).closure, ?_, hsub⟩
  exact isBounded_iff_forall_norm_le.mpr ⟨1, fun x hx => (hEsphere (hsub hx)).le⟩

end Tingley

end

end OAI
