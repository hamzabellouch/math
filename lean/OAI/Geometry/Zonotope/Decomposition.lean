import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

namespace OAI

/-!
The unit cube extruded by the segment from zero to the all-ones vector.
Its decomposition uses the cube and one extrusion cell for every upper facet.
The set definitions are literal subsets of a finite real coordinate space.
-/

noncomputable section
open Set

namespace DiagonalZonotope

variable {ι : Type*}

/-- The actual unit cube in the coordinate space. -/
def cube : Set (ι → ℝ) := {x | ∀ j, 0 ≤ x j ∧ x j ≤ 1}

/-- The Minkowski sum of the unit cube and the diagonal unit segment. -/
def zonotope : Set (ι → ℝ) :=
  {x | ∃ q ∈ cube, ∃ t ∈ Icc (0 : ℝ) 1, x = q + t • (1 : ι → ℝ)}

/-- The extrusion of the upper facet normal to coordinate `i`. -/
def cell (i : ι) : Set (ι → ℝ) :=
  {x | 1 ≤ x i ∧ x i ≤ 2 ∧ ∀ j, x i - 1 ≤ x j ∧ x j ≤ x i}

lemma cube_subset_zonotope : (cube : Set (ι → ℝ)) ⊆ zonotope := by
  intro x hx
  refine ⟨x, hx, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, zero_mul, add_zero]

lemma cell_subset_zonotope (i : ι) : cell i ⊆ zonotope := by
  intro x hx
  rcases hx with ⟨hlo, hhi, hcoord⟩
  refine ⟨fun j => x j - (x i - 1), ?_, x i - 1, ?_, ?_⟩
  · intro j
    constructor <;> linarith [(hcoord j).1, (hcoord j).2]
  · constructor <;> linarith
  · funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact (sub_add_cancel _ _).symm

/-- Decompose the actual diagonal extrusion by a maximal coordinate. -/
theorem zonotope_decomposition [Fintype ι] :
    (zonotope : Set (ι → ℝ)) = cube ∪ ⋃ i, cell i := by
  classical
  apply Subset.antisymm
  · intro x hx
    by_cases hc : x ∈ cube
    · exact Or.inl hc
    · rcases hx with ⟨q, hq, t, ht, hxt⟩
      have heq (j : ι) : x j = q j + t := by
        simpa using congrFun hxt j
      have hnonneg (j : ι) : 0 ≤ x j := by
        rw [heq j]
        exact add_nonneg (hq j).1 ht.1
      have hlarge : ∃ k, 1 < x k := by
        by_contra h
        push Not at h
        exact hc (fun j => ⟨hnonneg j, h j⟩)
      obtain ⟨k, hk⟩ := hlarge
      obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x
        ⟨k, Finset.mem_univ k⟩
      have hmax' (j : ι) : x j ≤ x i := hmax j (Finset.mem_univ j)
      right
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      refine ⟨by linarith [hmax' k], ?_, ?_⟩
      · linarith [heq i, (hq i).2, ht.2]
      · intro j
        exact ⟨by linarith [heq i, heq j, (hq i).2, (hq j).1], hmax' j⟩
  · intro x hx
    rcases hx with hc | hc
    · exact cube_subset_zonotope hc
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact cell_subset_zonotope i hi

/-- The cube and an upper-facet extrusion meet only in that facet's hyperplane. -/
theorem cube_inter_cell_subset (i : ι) :
    (cube : Set (ι → ℝ)) ∩ cell i ⊆ {x | x i = 1} := by
  intro x hx
  exact le_antisymm (hx.1 i).2 hx.2.1

/-- Distinct extrusion cells meet only on a coordinate-equality hyperplane. -/
theorem cell_inter_cell_subset (i j : ι) :
    cell i ∩ cell j ⊆ {x : ι → ℝ | x i = x j} := by
  intro x hx
  exact le_antisymm (hx.2.2.2 i).2 (hx.1.2.2 j).2

section AffineCell
variable [DecidableEq ι]

/-- A shear of the cube followed by translation by the `i`th unit vector. -/
def extrusionMap (i : ι) (s : ι → ℝ) : ι → ℝ :=
  fun j => if j = i then 1 + s i else s j + s i

/-- Each extrusion cell is an actual affine image of the unit cube. -/
theorem cell_eq_image_cube (i : ι) : cell i = extrusionMap i '' cube := by
  apply Subset.antisymm
  · intro x hx
    let s : ι → ℝ := fun j => if j = i then x i - 1 else x j - (x i - 1)
    refine ⟨s, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simp only [s, ite_eq_left rfl]
        constructor <;> linarith [hx.1, hx.2.1]
      · simp only [s, ite_eq_right hji]
        constructor <;> linarith [(hx.2.2 j).1, (hx.2.2 j).2]
    · funext j
      by_cases hji : j = i
      · subst j
        simp [extrusionMap, s]
      · simp [extrusionMap, s, hji]
  · rintro x ⟨s, hs, rfl⟩
    have hi : extrusionMap i s i = 1 + s i := by simp [extrusionMap]
    refine ⟨?_, ?_, ?_⟩
    · rw [hi]
      linarith [(hs i).1]
    · rw [hi]
      linarith [(hs i).2]
    · intro j
      by_cases hji : j = i
      · subst j
        exact ⟨by linarith, le_rfl⟩
      · simp only [extrusionMap, ite_eq_right hji, ite_true]
        constructor <;> linarith [(hs j).1, (hs j).2]

end AffineCell
end DiagonalZonotope

end

end OAI
