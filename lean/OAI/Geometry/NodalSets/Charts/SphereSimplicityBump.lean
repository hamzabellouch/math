import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.SeedCoordPatchTopology

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_sphere_simplicity_bump {r : ℝ} (hr : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (zeta : Yau.Jets.Coord → ℝ) (Z : Base → ℝ) (s : ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧ ContDiff ℝ ∞ zeta ∧ tsupport zeta ⊆ Q ∧
      (∀ x, 0 ≤ zeta x ∧ zeta x ≤ 1) ∧ 0 < s ∧
      (∀ x ∈ closedBall (0 : Yau.Jets.Coord) s, zeta x = 1) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ Z ∧ tsupport Z ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, Z (seedSphereFromCoord x) = zeta x) ∧ (∀ p, 0 ≤ Z p) ∧
      ∃ U : Set Base, IsOpen U ∧ U.Nonempty ∧ U ⊆ seedSpherePatch r ∧ ∀ p ∈ U, 0 < Z p := by
  have hzero : (0 : Yau.Jets.Coord) ∈ seedCoordPatch r := by
    simp [seedCoordPatch,hr]
  obtain ⟨e,he,hes⟩ := Metric.isOpen_iff.mp (seedCoordPatch_open r) 0 hzero
  have he2 : 0 < e/2 := half_pos he
  have hball : closedBall (0 : Yau.Jets.Coord) (e/2) ⊆ seedCoordPatch r :=
    (closedBall_subset_ball (by linarith)).trans hes
  obtain ⟨zeta,hz,hzc,hzs,hzr,hz1⟩ := compact_smooth_cutoff
    (isCompact_closedBall (0 : Yau.Jets.Coord) (e/2)) (seedCoordPatch_open r) hball
  obtain ⟨Z,hZ,hZs,hZval⟩ := seed_chart_scalar_extension zeta hz hzc
  have hZn (p : Base) : 0 ≤ Z p := by
    by_cases hp : p ∈ tsupport Z
    · obtain ⟨x,hx,rfl⟩ := hZs hp
      rw [hZval]
      exact (hzr x).1
    · rw [image_eq_zero_of_notMem_tsupport hp]
  refine ⟨tsupport zeta,zeta,Z,e/2,hzc,hzs,hz,Subset.rfl,hzr,he2,
    (fun x hx ↦ (hz1 x hx).eq_of_nhds),hZ,hZs,hZval,hZn,
    Z ⁻¹' Ioi 0,isOpen_Ioi.preimage hZ.continuous,?_,?_,fun p hp ↦ hp⟩
  · refine ⟨seedSphereFromCoord 0,?_⟩
    change 0 < Z (seedSphereFromCoord 0)
    rw [hZval,(hz1 0 (mem_closedBall_self he2.le)).eq_of_nhds]
    norm_num
  · intro p hp
    have hn : Z p ≠ 0 := (show 0 < Z p from hp).ne'
    obtain ⟨x,hx,rfl⟩ := hZs (subset_closure hn)
    exact ⟨seedCoordEquiv x,hzs hx,rfl⟩

end
end Yau.Target

end OAI
