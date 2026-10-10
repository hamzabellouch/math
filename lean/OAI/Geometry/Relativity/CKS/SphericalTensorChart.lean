import OAI.Geometry.Relativity.CKS.SphericalTensor

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

def tensorA (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (thetaFrame x) (thetaFrame x)
def tensorB (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (thetaFrame x) (phiUnit x)
def tensorC (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (phiUnit x) (phiUnit x)
def tensorPhi (T : E → Mat) (x : Point) := Real.sin (x 1) * tensorB T x

lemma tensorA_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorA T) := pair_smooth hT thetaFrame_smooth thetaFrame_smooth
lemma tensorB_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorB T) := pair_smooth hT thetaFrame_smooth phiUnit_smooth
lemma tensorC_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorC T) := pair_smooth hT phiUnit_smooth phiUnit_smooth
lemma tensorPhi_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorPhi T) := ((coord 1).contDiff.sin).mul (tensorB_smooth hT)

lemma frame_derivatives {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0) (x : Point) :
    D (basis 1) (tensorA T) x = dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) (thetaFrame x) ∧
    D (basis 2) (tensorA T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (thetaFrame x) +
      2 * Real.cos (x 1) * tensorB T x ∧
    D (basis 1) (tensorB T) x = dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) (phiUnit x) ∧
    D (basis 2) (tensorB T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (phiUnit x) +
      Real.cos (x 1) * (tensorC T x - tensorA T x) ∧
    D (basis 2) (tensorC T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (phiUnit x) (phiUnit x) -
      2 * Real.cos (x 1) * tensorB T x := by
  have hn (v : E) : pair (T (sphereParam x)) (sphereParam x) v = 0 :=
    pair_normal _ _ _ (hN _ (sphereParam_norm x))
  have hs (v w : E) := pair_symm (T (sphereParam x)) (hS _ (sphereParam_mem x)) v w
  have hr (v : E) : pair (T (sphereParam x)) v (sphereParam x) = 0 := by rw [hs,hn]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold tensorA
    rw [pair_derivative hT thetaFrame_smooth thetaFrame_smooth,theta_theta]
    simp only [pair_neg_left,pair_neg_right,hn,hr,neg_zero,zero_add,chartVector,Matrix.cons_val_one,Matrix.cons_val_zero]
  · unfold tensorA
    rw [pair_derivative hT thetaFrame_smooth thetaFrame_smooth,theta_phi]
    change pair (T (sphereParam x)) (Real.cos (x 1) • phiUnit x) (thetaFrame x) +
      pair (T (sphereParam x)) (thetaFrame x) (Real.cos (x 1) • phiUnit x) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (thetaFrame x) (thetaFrame x) = _
    rw [pair_smul_left,pair_smul_right,dPair_smul_dir,hs (phiUnit x) (thetaFrame x)]
    unfold tensorB
    ring
  · unfold tensorB
    rw [pair_derivative hT thetaFrame_smooth phiUnit_smooth,theta_theta,unit_theta]
    simp only [pair_neg_left,hn,neg_zero,pair_zero_right,zero_add,chartVector,Matrix.cons_val_one,Matrix.cons_val_zero]
  · unfold tensorB
    rw [pair_derivative hT thetaFrame_smooth phiUnit_smooth,theta_phi,unit_phi,equator_decomposition]
    change pair (T (sphereParam x)) (Real.cos (x 1) • phiUnit x) (phiUnit x) +
      pair (T (sphereParam x)) (thetaFrame x) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (thetaFrame x) (phiUnit x) = _
    simp only [pair_smul_left,pair_neg_right,pair_add_right,pair_smul_right,dPair_smul_dir,hr,mul_zero,zero_add]
    unfold tensorA tensorC
    ring
  · unfold tensorC
    rw [pair_derivative hT phiUnit_smooth phiUnit_smooth,unit_phi,equator_decomposition]
    change pair (T (sphereParam x)) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) (phiUnit x) +
      pair (T (sphereParam x)) (phiUnit x) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (phiUnit x) (phiUnit x) = _
    simp only [pair_neg_left,pair_add_left,pair_smul_left,pair_neg_right,pair_add_right,
      pair_smul_right,dPair_smul_dir,hr,hn,mul_zero,zero_add]
    rw [hs (phiUnit x) (thetaFrame x)]
    unfold tensorB
    ring

lemma tensor_trace_free {T : E → Mat}
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0) : tensorC T = fun x => -tensorA T x := by
  funext x
  have h := pair_trace (T (sphereParam x)) x (hN _ (sphereParam_norm x))
  rw [hTr _ (sphereParam_norm x)] at h
  change tensorA T x + tensorC T x = 0 at h
  linarith

end
end CKSSphericalChart

end

end OAI
