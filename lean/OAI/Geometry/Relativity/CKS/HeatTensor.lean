import OAI.Geometry.Relativity.CKS.HeatPotential
import OAI.Geometry.Relativity.CKS.RoundCasimir

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

lemma sphereGradient_rotations (F : E → ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    sphereGradient F x j = ∑ i : Ix, x i * smoothRotation i j F x := by
  simp only [sphereGradient, proj, grad, smoothRotation_pd, sub_mul, ite_mul,
    one_mul, zero_mul, sum_sub_distrib, sum_ite_eq, Finset.mem_univ, ite_true]
  rw [show (∑ i, x i * (x i * pd j F x - x j * pd i F x)) =
    (∑ i, x i ^ 2) * pd j F x - ∑ i, x j * x i * pd i F x by
      rw [sum_mul, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      ring, unit_sum_sq hx, one_mul]

lemma smoothRotation_congr_sphere {F G : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (h : ∀ x : E, ‖x‖ = 1 → F x = G x) {x : E} (hx : ‖x‖ = 1) (i j : Ix) :
    smoothRotation i j F x = smoothRotation i j G x := by
  by_cases hij : i = j
  · subst j
    simp [smoothRotation_pd]
  let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
  have he : (fun t => F (planeRotation i j hij t x)) =
      fun t => G (planeRotation i j hij t x) := by
    funext t
    apply h
    rw [(planeRotation i j hij t).norm_map, hx]
  have hFd := smoothRotation_orbit_derivative hF i j hij s 0
  have hGd := smoothRotation_orbit_derivative hG i j hij s 0
  change HasDerivAt (fun t => F (planeRotation i j hij t x)) _ 0 at hFd
  rw [he] at hFd
  simpa only [s, planeRotation_zero] using hFd.unique hGd

lemma sphereGradient_congr_sphere {F G : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (h : ∀ x : E, ‖x‖ = 1 → F x = G x) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    sphereGradient F x j = sphereGradient G x j := by
  rw [sphereGradient_rotations F hx, sphereGradient_rotations G hx]
  apply sum_congr rfl
  intro i hi
  rw [smoothRotation_congr_sphere hF hG h hx i j]

def heatTensor (p : ℕ → Poly) (t : ℝ) (x : E) : Mat :=
  traceFreeHess (spatialHeat (inversePolynomials p) (0,[]) t) x

lemma heatTensor_symmetric (p : ℕ → Poly) (hp : PolynomialRapid p)
    (t : ℝ) {x : E} (hx : ‖x‖ = 1) (i j : Ix) :
    heatTensor p t x i j = heatTensor p t x j i := by
  have hn : x ∈ U := by intro h; simp [h] at hx
  exact hessTF_symm _ _ (fun a b => partial_comm
    (spatialHeat_smooth _ (inversePolynomials_rapid p hp) _ t) hn a b) i j

lemma heatTensor_tangent (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    ∑ i : Ix, x i * heatTensor p t x i j = 0 :=
  hessTF_normal_left (unit_sum_sq hx) _ j

lemma heatTensor_trace_zero (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ∑ i : Ix, heatTensor p t x i i = 0 :=
  hessTF_trace_zero (unit_sum_sq hx) _

theorem heatTensor_divergence (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (t : ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    tensorDivergence (heatTensor p t) x j =
      sphereGradient (spatialHeat p (0,[]) t) x j := by
  have hi := spatialHeat_smooth _ (inversePolynomials_rapid p hp) (0,[]) t
  change tensorDivergence (traceFreeHess (spatialHeat (inversePolynomials p) (0,[]) t)) x j = _
  rw [divergence_traceFreeHess hi hx]
  apply sphereGradient_congr_sphere (hi.add ((roundLaplacian_smooth hi).div_const 2))
    (spatialHeat_smooth p hp _ t) _ hx j
  intro y hy
  rw [roundLaplacian_eq_Casimir hi hy]
  exact spatialHeat_inverse_equation p hp hh _ t (by intro h; simp [h] at hy)

end
end CKSInducedSphere

end

end OAI
