import OAI.Geometry.NodalSets.Charts.MetricCoercivity
import OAI.Geometry.NodalSets.Elliptic.LocalDirectionBounds
import OAI.Geometry.NodalSets.Waves.LatticeLogJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

include a in
theorem original_covariance_geometry : ∃ mu > 0, ∃ B > 0, ∀ x ∈ D,
    ‖g x‖ ≤ B ∧ ‖fderiv ℝ S x‖ ≤ B ∧ ∀ v, mu*‖v‖^2 ≤ g x v v := by
  let y := coverSourceCenter a.cover
  have hy := continuous_coverSourceCenter a.cover
  obtain ⟨mu,hmu,B,hB,hg⟩ := uniform_metric_coercivity (a.G ∘ y)
    (a.smooth_G.continuous.comp hy) (fun t ↦ a.positive_G (y t))
  have hc : Continuous (fun t ↦ fderiv ℝ a.A (y t)) :=
    (a.smooth_A.continuous_fderiv (by simp)).comp hy
  obtain ⟨M,hM,hm⟩ := (isCompact_univ.image hc).isBounded.exists_pos_norm_le
  refine ⟨mu,hmu,B+M,by positivity,?_⟩
  intro x hx
  let t := selectFrame a.cover ⟨x,hx⟩
  have he : y t = x := selectFrame_center a.cover ⟨x,hx⟩
  have hG := hg t
  change ‖a.G (y t)‖ ≤ B ∧ ∀ v, mu*‖v‖^2 ≤ a.G (y t) v v at hG
  rw [he] at hG
  have hA := hm _ ⟨t,mem_univ _,rfl⟩
  change ‖fderiv ℝ a.A (y t)‖ ≤ M at hA
  rw [he] at hA
  obtain ⟨hge,_,hae⟩ := a.germ x (a.centers_E hx)
  rw [hge.self_of_nhds] at hG
  rw [hae.fderiv_eq] at hA
  exact ⟨hG.1.trans (by linarith),hA.trans (by linarith),hG.2⟩

theorem lattice_eta_bounds {U : Set Coord} (hUD : U ⊆ D) :
    ∃ e > 0, ∃ E > 0, ∀ n (z : SourceGrid U n) j,
      e ≤ a.latticeEta hUD n z j ∧ a.latticeEta hUD n z j ≤ E := by
  obtain ⟨_,_,e,he,E,hE,hb⟩ := a.original_direction_bounds
  refine ⟨e,he,E,hE,?_⟩
  intro n z j
  exact (hb (latticeFrame a.cover hUD n z)).2 j

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
