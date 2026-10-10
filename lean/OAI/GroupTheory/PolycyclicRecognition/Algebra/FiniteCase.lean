import OAI.GroupTheory.PolycyclicRecognition.Algebra.Polycyclic
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

/-!
# The finite comparison case

The lower quasi-isometry inequality and finiteness of word-metric balls imply
that a group quasi-isometric to a finite group is finite. This treats the
zero-dimensional lattice case directly. No recognition theorem is assumed.
-/

namespace PolycyclicRecognition

variable {H P : Type*} [Group H] [PseudoMetricSpace H] [PseudoMetricSpace P]

/-- A coarsely embedded space with finite metric balls is finite when the target
is finite. The displayed inequality is the lower quasi-isometry inequality,
rearranged to avoid division by its multiplicative constant. -/
theorem finite_of_coarseEmbedding_finite [Finite P]
    (hballs : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    (f : H → P) (K C : ℝ) (hK : 0 ≤ K)
    (hlower : ∀ h k, dist h k ≤ K * dist (f h) (f k) + C) : Finite H := by
  obtain ⟨R, hR⟩ := (Set.finite_range (fun p : P => dist (f 1) p)).bddAbove
  have hbounded : Set.univ ⊆ Metric.closedBall (1 : H) (K * R + C) := by
    intro h _
    rw [Metric.mem_closedBall, dist_comm]
    calc
      dist 1 h ≤ K * dist (f 1) (f h) + C := hlower 1 h
      _ ≤ K * R + C := add_le_add (mul_le_mul_of_nonneg_left
        (hR (Set.mem_range_self (f h))) hK) le_rfl
  exact Set.finite_univ_iff.mp ((hballs (K * R + C)).subset hbounded)

/-- The finite-target special case of virtual-polycyclic recognition. -/
theorem virtuallyPolycyclic_of_coarseEmbedding_finite [Finite P]
    (hballs : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    (f : H → P) (K C : ℝ) (hK : 0 ≤ K)
    (hlower : ∀ h k, dist h k ≤ K * dist (f h) (f k) + C) :
    IsVirtuallyPolycyclic H := by
  have := finite_of_coarseEmbedding_finite hballs f K C hK hlower
  exact isVirtuallyPolycyclic_of_finite

end PolycyclicRecognition

end OAI
