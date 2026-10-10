import Mathlib

namespace OAI

universe uIndex uX

noncomputable section

open Filter Metric Set

namespace Problem356.Geometry

/-- A finite family of positive radii admits a common positive lower bound,
including when the indexing type is empty. -/
theorem exists_uniform_positive_radius {ι : Type uIndex} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · apply (Finset.lt_min'_iff s hs).2
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hr i
  · intro i
    exact Finset.min'_le s (r i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- A common ball around a point contained in finitely many open sets.
This applies to the open images of the local inverse branches. -/
theorem finite_common_ball {ι : Type uIndex} {X : Type uX} [Finite ι] [PseudoMetricSpace X]
    (a : X) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (ha : ∀ i, a ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, ball a δ ⊆ U i := by
  have hopen : IsOpen (⋂ i, U i) := isOpen_iInter_of_finite hU
  have hamem : a ∈ ⋂ i, U i := mem_iInter.mpr ha
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen a hamem
  exact ⟨δ, hδ, fun i x hx => mem_iInter.mp (hsub hx) i⟩

/-- Distinct finitely many centers admit a common positive radius with
pairwise disjoint closed balls. -/
theorem finite_disjoint_closedBalls {ι : Type uIndex} {X : Type uX} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  let J := {q : ι × ι // q.1 ≠ q.2}
  let r : J → ℝ := fun q => dist (a q.val.1) (a q.val.2) / 3
  have hr : ∀ q, 0 < r q := by
    intro q
    exact div_pos (dist_pos.mpr (ha.ne q.property)) (by norm_num)
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  apply Metric.closedBall_disjoint_closedBall
  have h := hbound ⟨(i, j), hij⟩
  change δ ≤ dist (a i) (a j) / 3 at h
  linarith

/-- One radius may simultaneously separate all components and keep each
closed component ball inside a prescribed open neighborhood. -/
theorem finite_disjoint_closedBalls_subset {ι : Type uIndex} {X : Type uX} [Finite ι]
    [MetricSpace X] (a : ι → X) (ha : Function.Injective a)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (haU : ∀ i, a i ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, closedBall (a i) δ ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  have hlocal : ∀ i, ∃ r : ℝ, 0 < r ∧ ball (a i) r ⊆ U i := by
    intro i
    exact Metric.isOpen_iff.mp (hU i) (a i) (haU i)
  choose r hr hsub using hlocal
  obtain ⟨ε, hε, hεr⟩ := exists_uniform_positive_radius r hr
  obtain ⟨η, hη, hdisj⟩ := finite_disjoint_closedBalls a ha
  refine ⟨min (ε / 2) η, lt_min (half_pos hε) hη, ?_, ?_⟩
  · intro i x hx
    apply hsub i
    rw [mem_ball]
    have hx' : dist x (a i) ≤ min (ε / 2) η := hx
    have hsmall : min (ε / 2) η ≤ ε / 2 := min_le_left _ _
    have hri := hεr i
    linarith
  · intro i j hij
    exact (hdisj hij).mono
      (closedBall_subset_closedBall (min_le_right _ _))
      (closedBall_subset_closedBall (min_le_right _ _))

end Problem356.Geometry

end

end OAI
