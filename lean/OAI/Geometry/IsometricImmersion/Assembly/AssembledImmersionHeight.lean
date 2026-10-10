import OAI.Geometry.IsometricImmersion.Assembly.InitialAssemblyMetric
import OAI.Geometry.IsometricImmersion.Metrics.PatchTensorPositivity
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibilityRestriction
import OAI.Geometry.IsometricImmersion.Obstructions.UniversalPatchSelection

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation SmoothLocal.ODE

theorem every_assembled_local_immersion_has_actual_local_height
    {epsilon : ℝ} (he : 0 < epsilon) (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric initialAssemblyMetric eta a q).PosDef)
    {U : Set Coord} (hU : IsOpen U) (hUS : U ⊆ square) (h0 : (0 : Coord) ∈ U)
    (F : Coord → Ambient) (hF : IsometricOn (assembledPatchMetric initialAssemblyMetric eta) F U)
    (nmin kmin : ℕ) :
    ∃ a : PatchAddress, nmin ≤ a.1 ∧ kmin ≤ a.2.1 ∧
      ∃ b ∈ frontier (accumulatingDisk a.1), ∃ e : Ambient,
        IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
        (secondFundamental F e b).rank = 1 ∧ patchAddressCarrier a ⊆ U ∧
        PatchAdmissibleHeight (localPatchMetric initialAssemblyMetric eta a)
          (height (affinePullbackImmersion F (patchAddressCenter a) (patchAddressMatrix a)) e) := by
  let g := assembledPatchMetric initialAssemblyMetric eta
  have hg : SmoothPositiveOn g square := assembledPatchMetric_smoothPositive_of_local_metrics
    he initialAssemblyMetric_smoothPositiveOn eta hsmall hlocal
  have hgU : SmoothPositiveOn g U :=
    ⟨fun i j => (hg.1 i j).mono hUS,fun p hp => hg.2 p (hUS hp)⟩
  have hcurv (n : ℕ) (p : Coord) (hp : p ∈ accumulatingDisk n) :
      gaussianCurvature g p = gaussianCurvature initialAssemblyMetric p :=
    assembledPatchMetric_curvature_on_disk_of_local_metrics he initialAssemblyMetric_smoothPositiveOn
      coordinate_square_isOpen eta hsmall hlocal n hp (accumulatingDisk_subset_square n hp)
  have hK (n : ℕ) (p : Coord)
      (hp : p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n)) : gaussianCurvature g p < 0 := by
    have hi : p ∈ interior (accumulatingDisk n) := by
      simpa only [accumulatingDisk,interior_roundClosedDisk _ (accumulatingRadius_pos n)] using hp
    rw [hcurv n p (interior_subset hi)]
    exact initialAssemblyMetric_negative_on_disk_interior n hi
  have hKb (n : ℕ) (p : Coord) (hp : p ∈ frontier (accumulatingDisk n)) : gaussianCurvature g p = 0 := by
    have hdisk : p ∈ accumulatingDisk n := by
      simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
    rw [hcurv n p hdisk]
    exact initialAssemblyMetric_zero_on_disk_frontier n hp
  obtain ⟨n,hn,b,hb,e,hen,hne,hrank,R,k,hk,c,hc,hpatch,hadm⟩ :=
    every_local_immersion_has_admissible_oriented_patch hgU hF hU h0 hK hKb nmin kmin
  let a : PatchAddress := ⟨n,k,R,c,hc⟩
  refine ⟨a,hn,hk,b,hb,e,hen,hne,hrank,hpatch,?_⟩
  exact assembledPatchMetric_admissible_local initialAssemblyMetric eta a hadm

end SmoothLocal.Geometry

end

end OAI
