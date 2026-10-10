import OAI.Analysis.CircleDomains.Transfer.SourceAnchor

namespace OAI

/-! A bound on a Jordan boundary bounds its filled side. -/

open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem jordan_closure_subset_closedBall_of_frontier
    (H : ℂ ≃ₜ ℂ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbound : frontier (jordanInterior H) ⊆ closedBall c R) :
    closure (jordanInterior H) ⊆ closedBall c R := by
  have hinside : jordanInterior H ⊆ closedBall c R := by
    have h := open_subset_finite_jordan_fills_of_frontier_subset
      (fun _ : Unit => roundJordanAt c R hR) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
      (jordanInterior_isOpen H) ((isCompact_closure_jordanInterior H).isBounded.subset subset_closure)
      (show frontier (jordanInterior H) ⊆ ⋃ _ : Unit,
        closure (jordanInterior (roundJordanAt c R hR)) from by
        intro z hz
        exact mem_iUnion.mpr ⟨(), by rw [roundJordanAt_closure]; exact hbound hz⟩)
    simpa only [iUnion_const, roundJordanAt_closure] using h

  exact closure_minimal hinside isClosed_closedBall

end CircleDomainRigidity

end

end OAI
