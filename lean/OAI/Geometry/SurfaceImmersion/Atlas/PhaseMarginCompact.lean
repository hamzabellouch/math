import OAI.Geometry.SurfaceImmersion.Atlas.NoncriticalPhaseBudgets
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseNeighborhood
import OAI.Geometry.Immersion.ClosedSurface.DenominatorBounds
import OAI.Geometry.SurfaceImmersion.Atlas.RestrictedPhasePartition

namespace OAI

/-! A relative normal-length margin places every relevant point in a fixed
compact noncritical region, before the immersion or its fast scale is selected. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def phaseMarginCompact {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (ε : ℝ) : Compacts Base :=
  ⟨(K : Set Base) ∩ {x | ε ≤ 4*‖phaseDerivative φ x‖^2},
    K.isCompact.inter_right (isClosed_le continuous_const
      (continuous_const.mul ((continuous_phaseDerivative hφ).norm.pow 2)))⟩

lemma phaseMarginCompact_noncritical {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) {ε : ℝ} (hε : 0 < ε) {x : Base}
    (hx : x ∈ (phaseMarginCompact hφ K ε : Set Base)) : phaseDerivative φ x ≠ 0 := by
  intro hz
  have hh : ε ≤ 4*‖phaseDerivative φ x‖^2 := hx.2
  rw [hz,norm_zero] at hh
  norm_num at hh
  exact (not_le_of_gt hε) hh

lemma mem_phaseMarginCompact_of_relative_margin {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) {ε : ℝ} {x : Base} (hx : x ∈ (K : Set Base))
    (B : Fin 3 → RVec 4) (hB : B ≠ 0)
    (hm : ε*‖B‖ ≤ ‖secondQuadratic B (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖) :
    x ∈ (phaseMarginCompact hφ K ε : Set Base) :=
  ⟨hx,relative_margin_covector_sq B (phaseDerivative φ x) hB hm⟩

theorem fixed_margin_phase_partition {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset (phaseMarginCompact hφ K ε)) (c : t → NoncriticalPhaseChart φ)
      (J : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.source,
        ‖iteratedFDerivWithin ℝ j (c i).chart (c i).chart.source x‖ ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.target,
        ‖iteratedFDerivWithin ℝ j (c i).chart.symm (c i).chart.target x‖ ≤ J m) ∧
      Nonempty (PhasePartitions.CompactPhasePartition t
        (phaseMarginCompact hφ K ε : Set Base) (fun i => (c i).chart.source)) := by
  obtain ⟨t,c,J,hcover,hJ,hf,hi⟩ := noncritical_phase_cover_budgets hφ
    (phaseMarginCompact hφ K ε) (fun _ hx => phaseMarginCompact_noncritical hφ K hε hx)
  exact ⟨t,c,J,hJ,hf,hi,PhasePartitions.exists_compact_phase_partition
    (phaseMarginCompact hφ K ε).isCompact _ (fun i => (c i).chart.open_source) hcover⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
