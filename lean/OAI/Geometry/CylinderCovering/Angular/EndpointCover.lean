import OAI.Geometry.CylinderCovering.Angular.EndpointCoverDefinitions
import OAI.Geometry.CylinderCovering.Angular.Endpoint
import OAI.Geometry.CylinderCovering.Angular.SampledCover

namespace OAI

noncomputable section
open Set

namespace AngularEndpoint

lemma profile_eq_d (q : ℝ) : profile q = TriangularCovering.d q := by
  unfold profile TriangularCovering.d
  ring

theorem endpoint_cover : CylinderCovering.AngularEndpointStatement := by
  intro k hk
  have hk0 : 0 < k := by omega
  have hN : 0 < k^2 := pow_pos hk0 2
  have hkreal : (14000:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have he0 : 0 < 1/(k:ℝ) := by positivity
  have he1 : 1/(k:ℝ) ≤ 1/14000 := by
    exact one_div_le_one_div_of_le (by norm_num) hkreal
  let L : ℕ → ℝ := fun j => if j=k^2+1 then 0 else
    alpha (k^2) j-boundary (k^2) j*beta (k^2) j
  have hL0 : L 0 = 0 := by
    simp only [L,show (0:ℕ) ≠ k^2+1 by omega,ite_false,coefficient_outer_left]
  have hLn : L (k^2+1) = 0 := by simp [L]
  have hleft : ∀ j < k^2+1,
      TriangularCovering.AngularSampling.nodeAlpha (node (k^2) j) -
        boundary (k^2) j*TriangularCovering.AngularSampling.nodeBeta (node (k^2) j) = L j := by
    intro j hj
    simp only [L,show j≠k^2+1 by omega,ite_false]
    rfl
  have hright : ∀ j < k^2+1,
      TriangularCovering.AngularSampling.nodeAlpha (node (k^2) j) -
        boundary (k^2) (j+1)*TriangularCovering.AngularSampling.nodeBeta (node (k^2) j) = L (j+1) := by
    intro j hj
    change alpha (k^2) j-boundary (k^2) (j+1)*beta (k^2) j = _
    by_cases hlast : j=k^2
    · subst j
      simpa [L] using coefficient_outer_right hN
    · have hjN : j<k^2 := by omega
      simp only [L,show j+1≠k^2+1 by omega,ite_false]
      have hc := coefficient_compatibility (show 0<j+1 by omega) (show j+1≤k^2 by omega)
      simp only [Nat.add_sub_cancel] at hc
      nlinarith only [hc]
  have hv : ∀ j, j≤k^2+1 → |boundary (k^2) j|≤1 := by
    intro j hj
    exact abs_le.mpr (boundary_bounds hN hj)
  have hinc : ∀ j<k^2+1, boundary (k^2) j<boundary (k^2) (j+1) := by
    intro j hj
    exact sector_width_pos hN (by omega)
  have hq : ∀ j<k^2+1,
      boundary (k^2) j≤node (k^2) j ∧ node (k^2) j≤boundary (k^2) (j+1) := by
    intro j hj
    exact node_in_sector hN (by omega)
  have hmesh : ∀ j<k^2+1, ∀ p∈Icc (boundary (k^2) j) (boundary (k^2) (j+1)),
      |node (k^2) j-p| ≤ (1/(k:ℝ))^2 := by
    intro j hj p hp
    rw [abs_sub_comm]
    exact (reciprocal_mesh_errors hk0 (by omega) hp).1
  obtain ⟨C,hpres,hcover,harea,hcost,hrel⟩ :=
    TriangularCovering.AngularSampling.compatible_sampled_cover
      (show 0<k^2+1 by omega) (boundary (k^2)) (node (k^2)) L
      (boundary_zero _) (boundary_last _) hv hinc hq hL0 hLn hleft hright he0 he1 hmesh
  refine ⟨C,?_,hcover,harea,hcost,hrel⟩
  convert hpres using 1 <;> funext j
  · rfl
  · rfl
  · unfold radius TriangularCovering.η
    rw [profile_eq_d]
    ring

end AngularEndpoint

end

end OAI
