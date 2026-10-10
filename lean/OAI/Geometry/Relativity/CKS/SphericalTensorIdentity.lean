import OAI.Geometry.Relativity.CKS.SphericalDivergence
import OAI.Geometry.Relativity.CKS.SphericalTensorChart

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma tensorPhi_derivatives {T : E → Mat}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) (x : Point) :
    D (basis 1) (tensorPhi T) x = Real.cos (x 1) * tensorB T x + Real.sin (x 1) * D (basis 1) (tensorB T) x ∧
    D (basis 2) (tensorPhi T) x = Real.sin (x 1) * D (basis 2) (tensorB T) x := by
  have hd : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hB := (tensorB_smooth hT).differentiable (by simp) x
  have hc (k : Ix) : D (basis k) (fun y : Point => Real.sin (y 1)) x =
      Real.cos (x 1) * (if (1 : Ix) = k then 1 else 0) := by
    rw [D_sin _ hd]
    change Real.cos (x 1) * D (basis k) (coord 1) x = _
    rw [D_coord]
  constructor
  · unfold tensorPhi
    rw [D_mul _ hd.sin hB,hc]
    norm_num
    ring
  · unfold tensorPhi
    rw [D_mul _ hd.sin hB,hc,ite_eq_right (show (1 : Ix) ≠ 2 by decide)]
    ring

theorem tensor_chart_divergence {T : E → Mat}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0)
    (x : Point) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (tensorA T) x + D (basis 2) (tensorPhi T) x / Real.sin (x 1)^2 +
      2 * Real.cos (x 1) * tensorA T x / Real.sin (x 1) =
      ∑ j : Ix, thetaFrame x j * tensorDivergence T (sphereParam x) j) ∧
    (D (basis 1) (tensorPhi T) x - D (basis 2) (tensorA T) x +
      Real.cos (x 1) * tensorPhi T x / Real.sin (x 1) =
      Real.sin (x 1) * ∑ j : Ix, phiUnit x j * tensorDivergence T (sphereParam x) j) := by
  obtain ⟨hAθ,hAφ,hBθ,hBφ,hCφ⟩ := frame_derivatives hT hS hN x
  obtain ⟨hPθ,hPφ⟩ := tensorPhi_derivatives hT x
  have hC : tensorC T x = -tensorA T x := congrFun (tensor_trace_free hN hTr) x
  have hCd : D (basis 2) (tensorC T) x = -D (basis 2) (tensorA T) x := by
    rw [tensor_trace_free hN hTr,D_neg]
  rw [hCφ,hAφ] at hCd
  have hTraceD : dPair T (sphereParam x) (phiUnit x) (phiUnit x) (phiUnit x) =
      -dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (thetaFrame x) := by
    apply mul_left_cancel₀ hs
    linear_combination hCd
  constructor
  · rw [hAθ,hPφ,hBφ,hC,divergence_frame T x _ (theta_tangent x),
      dPair_symm hT hS (sphereParam_mem x) (phiUnit x) (phiUnit x) (thetaFrame x)]
    field_simp
    ring
  · rw [hPθ,hBθ,hAφ,divergence_frame T x _ (unit_tangent x),hTraceD]
    unfold tensorPhi
    field_simp
    ring

theorem tensor_chart_gradient {F : E → ℝ} {T : E → Mat}
    (hF : ContDiffOn ℝ ∞ F U)
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0)
    (hDiv : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, tensorDivergence T y j = sphereGradient F y j)
    (x : Point) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (tensorA T) x + D (basis 2) (tensorPhi T) x / Real.sin (x 1)^2 +
      2 * Real.cos (x 1) * tensorA T x / Real.sin (x 1) = D (basis 1) (fun y => F (sphereParam y)) x) ∧
    (D (basis 1) (tensorPhi T) x - D (basis 2) (tensorA T) x +
      Real.cos (x 1) * tensorPhi T x / Real.sin (x 1) = D (basis 2) (fun y => F (sphereParam y)) x) := by
  obtain ⟨hθ,hφ⟩ := tensor_chart_divergence hT hS hN hTr x hs
  simp only [hDiv _ (sphereParam_norm x)] at hθ hφ
  rw [gradient_test F x _ (theta_tangent x)] at hθ
  rw [gradient_test F x _ (unit_tangent x)] at hφ
  constructor
  · rw [angular_first hF]
    exact hθ
  · rw [angular_first hF]
    change _ = fderiv ℝ F (sphereParam x) (Real.sin (x 1) • phiUnit x)
    rw [map_smul,smul_eq_mul]
    exact hφ

end
end CKSSphericalChart

end

end OAI
