import OAI.MeasureTheory.Falconer.Recursion.ParentBinSelection
import OAI.MeasureTheory.Falconer.Estimates.DistanceFormRemoval

namespace OAI

namespace PlanarFalconer
open Set

theorem sourceConeCircle_one_near_centered_angle (axis : ℝ) {φ θ : ℝ}
    (hφ : |φ| ≤ 1/20) (hθ : |θ-φ| ≤ 1/20) :
    sourceConeCircle axis (sourceUnitDirection (θ+axis)) = 1 := by
  have ht : |θ| ≤ 1/10 := by
    have hh := abs_add_le (θ-φ) φ
    rw [sub_add_cancel] at hh
    linarith
  have hperiod : θ ∈ Ioc (-Real.pi) Real.pi := by
    have hh := abs_le.mp ht
    exact ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  simp only [sourceConeCircle, sourceCircleRotate_comp, add_neg_cancel_right,
    sourceAngle_comp_on_period hperiod]
  exact graphConeCutoff_one ht

theorem strong_separation_source_cutoff (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    ∃ φ : ℝ, |φ| ≤ 1/20 ∧
      x-y = ‖x-y‖ • sourceDirection (φ+sourceParentAxis P Q) ∧
      ∀ θ : ℝ, |θ-φ| ≤ 1/20 →
        sourceConeCircle (sourceParentAxis P Q) (sourceUnitDirection (θ+sourceParentAxis P Q)) = 1 := by
  obtain ⟨φ,hφ,_,hΔ⟩ := strong_separation_parent_angle P Q hP hQ hp hq hl hx hy
  exact ⟨φ,hφ,hΔ,fun θ hθ => sourceConeCircle_one_near_centered_angle _ hφ hθ⟩

theorem parent_bin_activity_iff (n j : ℕ) (X Y P Q : DyadicSquare) (radius : ℝ) :
    (∃ dir ∈ tsupport (fun dir => circleAngularBin n j
      (sourceCircleRotate (-sourceParentAxis X Y) dir)),
      dist (sourceRadialUnit Q.center P.center) dir < radius) ↔
      AngularBinActive n j (sourceCenteredCellDirection X Y P Q) radius := by
  have hh := rotated_bin_activity_iff n j (sourceParentAxis X Y)
    (sourceCenteredCellDirection X Y P Q) radius
  simpa only [sourceCenteredCellDirection, sourceCircleRotate_add, neg_add_cancel,
    sourceCircleRotate_zero] using hh

theorem parent_inactive_selection_capped {sig κ c₀ : ℝ}
    (hgap : 10*sig < κ) (hc : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℝ, κ*(N:ℝ) ≤ t →
    ∀ (X Y : DyadicSquare) (A B : CellPath),
      sourceParentInactiveSelection N sig t X Y A B =
        rotatedBinSelection (angularBinCount (graphAngularScale N sig t c₀))
          (inactiveAngularLabels (angularBinCount (graphAngularScale N sig t c₀))
            (sourceCenteredCellDirection X Y (X.descendant A) (Y.descendant B))
            (3*graphAngularScale N sig t c₀)) (sourceParentAxis X Y) := by
  obtain ⟨N₀,hN₀⟩ := graphAngularScale_cap_inactive hgap hc
  refine ⟨N₀,?_⟩
  intro N hN t ht X Y A B
  rw [hN₀ N hN t ht]
  rfl

end PlanarFalconer

end OAI
