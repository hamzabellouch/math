import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.NativeLaws

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupBranchLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

theorem jointCounts_branch_pos {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (b : w.1.Branch)
    (hb : 0 < (branchLaw w.1).mass b) :
    0 < jointCounts allocation dilation w (branchShape w b) := by
  have hp : 0 < (population allocation dilation (w.1.source, w.2) : ℝ) := by
    exact_mod_cast work_source_population_pos allocation hd w
  have hc : 0 < (jointCounts allocation dilation w (branchShape w b) : ℝ) := by
    rw [jointCounts_cast, placedLaw_mass_branch]
    exact mul_pos hp hb
  exact_mod_cast hc

theorem branchLaw_stageA_mass_pos {K : ℕ} (h : InitialPositive K)
    (b : (Work.stageA h).Branch) :
    0 < (branchLaw (Work.stageA h)).mass b := by
  change 0 < (stageALaw (initialShape h.val) (aSplit ⟨h, b, false⟩) : ℝ)
  exact_mod_cast stageALaw_positive _ _ (aSplit_mem ⟨h, b, false⟩)

theorem branchLaw_stageB_mass_pos {K : ℕ} (h : APositive K)
    (b : (Work.stageB h).Branch) :
    0 < (branchLaw (Work.stageB h)).mass b := by
  change 0 < (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ)
  exact_mod_cast stageBLaw_positive _ _ (bSplit_mem ⟨h, b, false⟩)

theorem supportedHalfLaw_branchShape_of_mass_pos {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (right : Bool) (h : ActiveOrder K tick sigma)
    (b : h.val.val.1.Branch) (hb : 0 < (branchLaw h.val.val.1).mass b)
    (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  have hc : 0 < activeCounts allocation 1 h.val (branchShape h.val.val b) :=
    jointCounts_branch_pos allocation (by decide) h.val.val b hb
  rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right h.val _ hc]
  funext a
  rw [halfLawAt_eq, canonicalChildShape_branchShape, placement_symm_order_side]

theorem supportedHalfLaw_branchShape_of_mass_ne_zero {K tick : ℕ}
    {sigma : Placement} (allocation : Allocation) (right : Bool)
    (h : ActiveOrder K tick sigma) (b : h.val.val.1.Branch)
    (hb : (branchLaw h.val.val.1).mass b ≠ 0) (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  exact supportedHalfLaw_branchShape_of_mass_pos allocation right h b
    (lt_of_le_of_ne ((branchLaw h.val.val.1).nonneg b) (Ne.symm hb)) side

theorem weighted_supportedHalfLaw_branchShape {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (right : Bool) (h : ActiveOrder K tick sigma)
    (b : h.val.val.1.Branch) (side : Fin 3) (a : Statistic h.val) :
    (branchLaw h.val.val.1).mass b *
        supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) a =
      (branchLaw h.val.val.1).mass b *
        (h.val.val.1.childLaw
          (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
          (h.val.val.1.priority side) a : ℝ) := by
  by_cases hb : (branchLaw h.val.val.1).mass b = 0
  · simp only [hb, zero_mul]
  · rw [supportedHalfLaw_branchShape_of_mass_ne_zero allocation right h b hb side]

end MatrixMultiplication.AllFieldGroupBranchLaws

end

end OAI
