import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization

namespace OAI

/-! The actual compact region on which a finite-hole differential form
must be retained, including its outer and circular boundary curves. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma finite_hole_core_closed (H : ℂ ≃ₜ ℂ) {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    IsClosed (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) :=
  isClosed_closure.sdiff (isOpen_iUnion fun _ => isOpen_ball)

lemma jordan_boundary_mem_finite_hole_core {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H) (t : ℝ) :
    γ t ∈ closure (jordanInterior H) \ ⋃ i, ball (c i) (r i) := by
  refine ⟨(hγ.mem_frontier t).1,?_⟩
  intro hm
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  have hiJ := hin i (ball_subset_closedBall hi)
  exact (hγ.mem_frontier t).2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hiJ)

lemma circle_mem_finite_hole_core (H : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H) (i : Fin n) (t : ℝ) :
    unitCircleParam (c i) (r i) t ∈ closure (jordanInterior H) \ ⋃ j, ball (c j) (r j) := by
  have hs : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) := by
    simpa only [unitCircleParam,abs_of_pos (hr i)] using
      circleMap_mem_sphere' (c i) (r i) (2*Real.pi*t)
  have hc : unitCircleParam (c i) (r i) t ∈ closedBall (c i) (r i) :=
    sphere_subset_closedBall hs
  refine ⟨subset_closure (hin i hc),?_⟩
  intro hm
  obtain ⟨j,hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have hdist : dist (unitCircleParam (c i) (r i) t) (c i) = r i := hs
    exact (not_lt_of_ge hdist.ge) hj
  · exact Set.disjoint_left.mp (hd hij) hc (ball_subset_closedBall hj)

end CircleDomainRigidity

end

end OAI
