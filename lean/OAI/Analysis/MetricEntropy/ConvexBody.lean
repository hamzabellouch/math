import OAI.Analysis.MetricEntropy.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

universe uι uX uY

/-!
# The concrete symmetric convex bodies

The absolute row hull is the convex hull of the actual finite set of rows and
their negatives. Adding a positive multiple of the coordinate cube gives full
ambient interior, without any spanning hypothesis on the rows.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

section Cube

variable {ι : Type uι} [Fintype ι]

theorem cube_eq_closedBall :
    cube ι = Metric.closedBall (0 : RealSpace ι) 1 := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)]
  simp only [cube, Set.mem_ofPred_eq, Real.norm_eq_abs]

theorem isCompact_cube : IsCompact (cube ι) := by
  rw [cube_eq_closedBall]
  exact isCompact_closedBall _ _

theorem convex_cube : Convex ℝ (cube ι) := by
  rw [cube_eq_closedBall]
  exact convex_closedBall _ _

omit [Fintype ι] in
theorem cube_symmetric (x : RealSpace ι) : x ∈ cube ι ↔ -x ∈ cube ι := by
  simp only [cube, Set.mem_ofPred_eq, Pi.neg_apply, abs_neg]

theorem zero_mem_interior_cube : (0 : RealSpace ι) ∈ interior (cube ι) := by
  rw [cube_eq_closedBall]
  exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num))

theorem cube_isSymmetricConvexBody : IsSymmetricConvexBody (cube ι) where
  isCompact := isCompact_cube
  convex := convex_cube
  symmetric := cube_symmetric
  interior_nonempty := ⟨0, zero_mem_interior_cube⟩

theorem zero_mem_interior_smul_cube {t : ℝ} (ht : t ≠ 0) :
    (0 : RealSpace ι) ∈ interior (t • cube ι) := by
  rw [interior_smul₀ ht]
  simpa only [smul_zero] using
    (Set.smul_mem_smul_set (a := t) (zero_mem_interior_cube (ι := ι)))

end Cube

section RowHull

variable {X : Type uX} {Y : Type uY} (g : Y → X → ℝ)

theorem convex_absRowHull : Convex ℝ (absRowHull g) :=
  convex_convexHull ℝ _

theorem absRowHull_symmetric (z : RealSpace Y) :
    z ∈ absRowHull g ↔ -z ∈ absRowHull g := by
  have hneg : absRowHull g ⊆ -absRowHull g := by
    apply convexHull_min _ (convex_absRowHull g).neg
    rintro w (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · apply Set.mem_neg.mpr
      exact subset_convexHull ℝ _ (Or.inr ⟨x, rfl⟩)
    · apply Set.mem_neg.mpr
      simpa only [absRowHull, neg_neg] using
        (subset_convexHull ℝ
          (Set.range (row g) ∪ Set.range (fun x => -row g x))
          (Or.inl ⟨x, rfl⟩))
  constructor
  · intro hz
    exact Set.mem_neg.mp (hneg hz)
  · intro hz
    simpa only [neg_neg] using Set.mem_neg.mp (hneg hz)

theorem zero_mem_absRowHull [Nonempty X] : (0 : RealSpace Y) ∈ absRowHull g := by
  let x : X := Classical.choice inferInstance
  have hx : row g x ∈ absRowHull g :=
    subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩)
  have hnx : -row g x ∈ absRowHull g := (absRowHull_symmetric g _).mp hx
  simpa only [smul_neg, add_neg_cancel] using
    (convex_absRowHull g hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1))

theorem isCompact_absRowHull [Fintype X] [Fintype Y] : IsCompact (absRowHull g) := by
  exact ((Set.finite_range (row g)).union
    (Set.finite_range (fun x => -row g x))).isCompact_convexHull ℝ

end RowHull

section MatrixBody

variable {X : Type uX} {Y : Type uY} [Fintype Y] (g : Y → X → ℝ) (t : ℝ)

theorem convex_matrixBody : Convex ℝ (matrixBody g t) :=
  ((convex_absRowHull g).smul (3 : ℝ)).add (convex_cube.smul t)

theorem isCompact_matrixBody [Fintype X] : IsCompact (matrixBody g t) :=
  ((isCompact_absRowHull g).smul (3 : ℝ)).add (isCompact_cube.smul t)

omit [Fintype Y] in
theorem matrixBody_symmetric (z : RealSpace Y) :
    z ∈ matrixBody g t ↔ -z ∈ matrixBody g t := by
  have hneg : ∀ w, w ∈ matrixBody g t → -w ∈ matrixBody g t := by
    intro w hw
    rcases Set.mem_add.mp hw with ⟨a, ha, b, hb, rfl⟩
    rcases Set.mem_smul_set.mp ha with ⟨u, hu, rfl⟩
    rcases Set.mem_smul_set.mp hb with ⟨v, hv, rfl⟩
    apply Set.mem_add.mpr
    refine ⟨(3 : ℝ) • (-u),
      Set.smul_mem_smul_set ((absRowHull_symmetric g u).mp hu),
      t • (-v), Set.smul_mem_smul_set ((cube_symmetric v).mp hv), ?_⟩
    simp only [smul_neg, neg_add]
  exact ⟨hneg z, fun hz => by simpa only [neg_neg] using hneg (-z) hz⟩

omit [Fintype Y] in
theorem smul_cube_subset_matrixBody [Nonempty X] : t • cube Y ⊆ matrixBody g t := by
  intro z hz
  apply Set.mem_add.mpr
  refine ⟨0, ?_, z, hz, zero_add z⟩
  simpa only [smul_zero] using
    (Set.smul_mem_smul_set (a := (3 : ℝ)) (zero_mem_absRowHull g))

omit [Fintype Y] in
theorem matrixBody_three_row_mem (x : X) : (3 : ℝ) • row g x ∈ matrixBody g t := by
  apply Set.mem_add.mpr
  refine ⟨(3 : ℝ) • row g x, ?_, 0, ?_, add_zero _⟩
  · exact Set.smul_mem_smul_set (subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩))
  · simpa only [smul_zero] using
      (Set.smul_mem_smul_set (a := t) (zero_mem_cube (ι := Y)))

theorem zero_mem_interior_matrixBody [Nonempty X] (ht : 0 < t) :
    (0 : RealSpace Y) ∈ interior (matrixBody g t) :=
  interior_mono (smul_cube_subset_matrixBody g t)
    (zero_mem_interior_smul_cube (ne_of_gt ht))

theorem matrixBody_isSymmetricConvexBody [Fintype X] [Nonempty X] (ht : 0 < t) :
    IsSymmetricConvexBody (matrixBody g t) where
  isCompact := isCompact_matrixBody g t
  convex := convex_matrixBody g t
  symmetric := matrixBody_symmetric g t
  interior_nonempty := ⟨0, zero_mem_interior_matrixBody g t ht⟩

end MatrixBody

end MetricEntropyDuality

end

end OAI
