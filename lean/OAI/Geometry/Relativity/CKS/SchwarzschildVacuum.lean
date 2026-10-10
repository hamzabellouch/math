import OAI.Geometry.Relativity.CKS.SchwarzschildVacuumSpherical

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSCalculus CKSRealizedRound CKSAngularGeometry CKSCartesianOuter
open CKSSphericalChart CKSSpatialManifold
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma cart_vacuum {m : ℝ} (hm : 0 < m) {y : E3} (hy : 2*m ≤ ‖y‖) :
    spatialDEC (cartMetric m) (cartTensor m) y ∧ spatialEnergy (cartMetric m) (cartTensor m) y = 0 := by
  have hyp : 0 < ‖y‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hy
  obtain ⟨x,hxr,hx⟩ := sphericalMap_surjective_radial y
  have hg : ContDiffAt ℝ ∞ (spatialCoefficients (cartMetric m)) (sphericalMap x) := by
    rw [hx]; exact spatialCoefficients_smooth (cartMetric_smoothAt hm hy)
  have hk : ContDiffAt ℝ ∞ (spatialCoefficients (cartTensor m)) (sphericalMap x) := by
    rw [hx]; exact spatialCoefficients_smooth (cartTensor_smoothAt hm hy)
  have hpositive := spatialCoefficients_positive (cartMetric_symm m y) (cartMetric_pos hm hy)
  have hdet : (spatialCoefficients (cartMetric m) (sphericalMap x)).det ≠ 0 := by
    rw [hx]; exact hpositive.det_pos.ne'
  have hreg (p : PhysicalPoint) (hpr : p 0 = x 0) (hs : Real.sin (p 1) ≠ 0) :=
    spherical_vacuum_regular (m := m) (show 0 < p 0 by rw [hpr,hxr]; exact hyp) hs
      (show 0 < lapseSquared m (p 0) by rw [hpr,hxr]; exact lapseSquared_pos hm hy)
  constructor
  · unfold spatialDEC
    rw [← hx]
    exact spherical_DEC_extend_poles hg hk hdet (fun p hp hs => (hreg p hp hs).1)
  · unfold spatialEnergy
    rw [← hx]
    have h := spherical_energy_bound_extend_poles hg hk hdet (b := 0)
      (fun p hp hs => by rw [(hreg p hp hs).2,abs_zero])
    exact abs_nonpos_iff.mp h

lemma physical_DEC {m : ℝ} (hm : 0 < m) :
    PhysicalDEC I3 (metricInner m) (tensorInner m) := by
  intro x
  refine ⟨univ,position m,cartMetric m,cartTensor m,isOpen_univ,mem_univ _,
    (position_smooth m).contMDiffOn,?_,?_,?_,?_,?_⟩
  · intro y _
    exact endInner_fullRank (smoothMetric hm) (position m) (cartMetric m) rfl
  · intro y _
    have hy : 2*m ≤ ‖position m y‖ := by rw [norm_position hm]; exact radius_ge m y
    exact ⟨cartMetric_smoothAt hm hy,cartTensor_smoothAt hm hy⟩
  · intro y _
    have hy : 2*m ≤ ‖position m y‖ := by rw [norm_position hm]; exact radius_ge m y
    exact ⟨cartMetric_symm m _,cartMetric_pos hm hy,cartTensor_symm m _⟩
  · exact fun y _ => ⟨rfl,rfl⟩
  · exact (cart_vacuum hm (by rw [norm_position hm]; exact radius_ge m x)).1
end CKSSchwarzschild

end

end OAI
