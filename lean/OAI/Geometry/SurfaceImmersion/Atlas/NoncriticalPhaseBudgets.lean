import OAI.Geometry.SurfaceImmersion.Atlas.NoncriticalPhaseCover
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds

namespace OAI

/-! Fixed coordinate budgets on the finite cover of a noncritical phase.
The immersion has no role in selecting these constants. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes WeightedEstimates

theorem noncritical_phase_cover_budgets {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (hφK : ∀ x ∈ (K : Set Base), phaseDerivative φ x ≠ 0) :
    ∃ (t : Finset K) (c : t → NoncriticalPhaseChart φ) (J : ℕ → ℝ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source ∧ (∀ m, 1 ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.source,
        ‖iteratedFDerivWithin ℝ j (c i).chart (c i).chart.source x‖ ≤ J m) ∧
      (∀ i m j, j ≤ m → ∀ x ∈ (c i).chart.target,
        ‖iteratedFDerivWithin ℝ j (c i).chart.symm (c i).chart.target x‖ ≤ J m) := by
  classical
  obtain ⟨t,c,hcover⟩ := finite_noncritical_phase_cover hφ K hφK
  choose D hD hd using fun (i : t) m => compact_local_weighted_bound
    (c i).chart.open_source isOpen_univ (c i).sourceCompact.isCompact (c i).sourceBound
    (subset_univ _) (c i).smooth.contDiffOn m
  choose E hE he using fun (i : t) m => compact_local_weighted_bound
    (c i).chart.open_target isOpen_univ (c i).targetCompact.isCompact (c i).targetBound
    (subset_univ _) (c i).smoothInverse.contDiffOn m
  let J := fun m => 1+∑ i : t, (D i m+E i m)
  have hJ (m) : 1 ≤ J m := by
    have hh : 0 ≤ ∑ i : t, (D i m+E i m) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (zero_le_one.trans (hD i m)) (zero_le_one.trans (hE i m)))
    exact le_add_of_nonneg_right hh
  have hDE (i : t) (m) : D i m ≤ J m ∧ E i m ≤ J m := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i : t => D i m+E i m)
      (fun i _ => add_nonneg (zero_le_one.trans (hD i m)) (zero_le_one.trans (hE i m))) (Finset.mem_univ i)
    have hs : D i m+E i m ≤ J m := hh.trans (le_add_of_nonneg_left zero_le_one)
    exact ⟨(le_add_of_nonneg_right (zero_le_one.trans (hE i m))).trans hs,
      (le_add_of_nonneg_left (zero_le_one.trans (hD i m))).trans hs⟩
  refine ⟨t,c,J,hcover,hJ,?_,?_⟩
  · intro i m j hj x hx
    have hh := hd i m 1 zero_le_one le_rfl j hj x hx
    simpa only [one_pow,one_mul] using hh.trans (hDE i m).1
  · intro i m j hj x hx
    have hh := he i m 1 zero_le_one le_rfl j hj x hx
    simpa only [one_pow,one_mul] using hh.trans (hDE i m).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
