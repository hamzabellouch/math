import OAI.Geometry.Relativity.CKS.SphericalFrame

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma sphereParam_mem (x : Point) : sphereParam x ∈ U := by
  intro h
  have hn := sphereParam_norm x
  simp [h] at hn

lemma angular_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiff ℝ ∞ (fun y => F (sphereParam y)) :=
  hF.comp_contDiff sphereParam_smooth sphereParam_mem

lemma second_eval {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {n : E} (hn : n ∈ U)
    (v w : E) : fderiv ℝ (fderiv ℝ F) n v w =
      ∑ i : Ix, ∑ j : Ix, v i * w j * hess F n i j := by
  conv_lhs => rw [CKSInducedSphere.expand_vec v, CKSInducedSphere.expand_vec w]
  simp only [map_sum,map_smul, _root_.sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, hess, CKSInducedSphere.partial_partial hF hn]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma angular_first {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    (D (basis i) (fun y => F (sphereParam y))) =
      fun y => fderiv ℝ F (sphereParam y) (chartVector i y) := by
  funext x
  rw [angular_chain (CKSInducedSphere.smooth_diff hF (sphereParam_mem x)),
    CKSInducedSphere.fderiv_expand]

lemma angular_second {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point) (i j : Ix) :
    D (basis j) (D (basis i) (fun y => F (sphereParam y))) x =
      fderiv ℝ F (sphereParam x) (fderiv ℝ (chartVector i) x (basis j)) +
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (chartVector j x) (chartVector i x) := by
  have hFd := hF.fderiv_of_isOpen (m := ∞) CKSInducedSphere.U_open (by simp)
  have hFc := hFd.comp_contDiff sphereParam_smooth sphereParam_mem
  have hf := CKSInducedSphere.smooth_diff hF (sphereParam_mem x)
  have hfd := (hFd.contDiffAt (CKSInducedSphere.U_open.mem_nhds (sphereParam_mem x))).differentiableAt (by simp)
  rw [angular_first hF]
  unfold D
  change fderiv ℝ (fun y => ((fderiv ℝ F) ∘ sphereParam) y (chartVector i y)) x (basis j) = _
  rw [fderiv_clm_apply (hFc.differentiable (by simp) x)
    ((chartVector_smooth i).differentiable (by simp) x)]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ (chartVector i) x (basis j)) +
    fderiv ℝ ((fderiv ℝ F) ∘ sphereParam) x (basis j) (chartVector i x) = _
  rw [fderiv_comp x hfd (sphereParam_smooth.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply,fderiv_sphereParam]

lemma phi_phi (x : Point) : fderiv ℝ phiFrame x (basis 2) =
    -(Real.sin (x 1) • equator x) := by
  unfold phiFrame
  rw [fderiv_fun_smul (show DifferentiableAt ℝ (fun y : Point => Real.sin (y 1)) x from
      ((coord 1).differentiableAt).sin) (phiUnit_smooth.differentiable (by simp) x)]
  have hz : fderiv ℝ (fun y : Point => Real.sin (y 1)) x (basis 2) = 0 := by
    change D (basis 2) (fun y : Point => Real.sin (y 1)) x = 0
    rw [D_sin _ (show DifferentiableAt ℝ (fun y : Point => y 1) x from (coord 1).differentiableAt)]
    change Real.cos (x 1) * D (basis 2) (coord 1) x = 0
    rw [D_coord]
    rw [ite_eq_right (show (1 : Ix) ≠ 2 by decide)]
    ring
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, unit_phi, hz, zero_smul, add_zero, smul_neg]

lemma laplacian_frame {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point) :
    roundLaplacian F (sphereParam x) =
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (thetaFrame x) (thetaFrame x) +
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (phiUnit x) (phiUnit x) -
      2 * fderiv ℝ F (sphereParam x) (sphereParam x) := by
  rw [second_eval hF (sphereParam_mem x), second_eval hF (sphereParam_mem x),
    CKSInducedSphere.fderiv_expand]
  unfold roundLaplacian CKSInducedSphere.roundLap CKSInducedSphere.tangentTrace
  simp only [projected_frame,add_mul,sum_add_distrib]

theorem angular_laplacian {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point)
    (hs : Real.sin (x 1) ≠ 0) :
    D (basis 1) (D (basis 1) (fun y => F (sphereParam y))) x +
      Real.cos (x 1) / Real.sin (x 1) * D (basis 1) (fun y => F (sphereParam y)) x +
      D (basis 2) (D (basis 2) (fun y => F (sphereParam y))) x / Real.sin (x 1)^2 =
      roundLaplacian F (sphereParam x) := by
  rw [angular_second hF, angular_second hF, angular_first hF, laplacian_frame hF]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ thetaFrame x (basis 1)) +
    fderiv ℝ (fderiv ℝ F) (sphereParam x) (thetaFrame x) (thetaFrame x) +
    Real.cos (x 1)/Real.sin (x 1) * fderiv ℝ F (sphereParam x) (thetaFrame x) +
    (fderiv ℝ F (sphereParam x) (fderiv ℝ phiFrame x (basis 2)) +
    fderiv ℝ (fderiv ℝ F) (sphereParam x) (phiFrame x) (phiFrame x)) / Real.sin (x 1)^2 = _
  rw [theta_theta,phi_phi,equator_decomposition]
  simp only [phiFrame,map_neg,map_add,map_smul,smul_apply,smul_eq_mul]
  field_simp
  ring

end
end CKSSphericalChart

end

end OAI
