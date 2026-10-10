import OAI.Geometry.Relativity.CKS.SphericalCharts

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma D_neg (v : Point) (f : Point → ℝ) (x : Point) :
    D v (fun y => -f y) x = -D v f x := by simp [D, fderiv_fun_neg]

def equator (x : Point) : E := WithLp.toLp 2 ![Real.cos (x 2),Real.sin (x 2),0]
lemma equator_smooth : ContDiff ℝ ∞ equator := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [equator] <;> fun_prop

lemma theta_theta (x : Point) : fderiv ℝ thetaFrame x (basis 1) = -sphereParam x := by
  ext j
  rw [component_fderiv (thetaFrame_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [thetaFrame,sphereParam]
  all_goals
    simp only [D_mul _ hd1.cos hd2.cos, D_mul _ hd1.cos hd2.sin,
      D_sin _ hd1,D_sin _ hd2,D_cos _ hd1,D_cos _ hd2,dc, D_neg,
      Fin.reduceEq,ite_true,ite_false]
    ring

lemma theta_phi (x : Point) : fderiv ℝ thetaFrame x (basis 2) = Real.cos (x 1) • phiUnit x := by
  ext j
  rw [component_fderiv (thetaFrame_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [thetaFrame,phiUnit]
  all_goals
    simp only [D_mul _ hd1.cos hd2.cos, D_mul _ hd1.cos hd2.sin,
      D_sin _ hd1,D_sin _ hd2,D_cos _ hd1,D_cos _ hd2,dc, D_neg,
      Fin.reduceEq,ite_true,ite_false]
    ring

lemma unit_theta (x : Point) : fderiv ℝ phiUnit x (basis 1) = 0 := by
  ext j
  rw [component_fderiv (phiUnit_smooth.differentiable (by simp) x)]
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [phiUnit]
  all_goals
    simp only [D_neg, D_sin _ hd2,D_cos _ hd2,dc,D_const, Fin.reduceEq, ite_false]
    <;> ring

lemma unit_phi (x : Point) : fderiv ℝ phiUnit x (basis 2) = -equator x := by
  ext j
  rw [component_fderiv (phiUnit_smooth.differentiable (by simp) x)]
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [phiUnit,equator]
  all_goals
    simp only [D_neg, D_sin _ hd2,D_cos _ hd2,dc,D_const, ite_true]
    ring

lemma equator_decomposition (x : Point) : equator x =
    Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x := by
  ext i
  fin_cases i <;> dsimp [equator,sphereParam,thetaFrame]
  · linear_combination -Real.cos (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · linear_combination -Real.sin (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · ring

lemma projected_frame (x : Point) (i j : Ix) :
    proj (fun k => sphereParam x k) i j =
      thetaFrame x i * thetaFrame x j + phiUnit x i * phiUnit x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [proj,sphereParam,thetaFrame,phiUnit,Fin.reduceEq]
  all_goals ring_nf <;> simp only [Real.sin_sq] <;> ring

lemma theta_tangent (x : Point) : ∑ i : Ix, sphereParam x i * thetaFrame x i = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.sin (x 1)*Real.cos (x 2))*(Real.cos (x 1)*Real.cos (x 2)) +
    (Real.sin (x 1)*Real.sin (x 2))*(Real.cos (x 1)*Real.sin (x 2)) +
    Real.cos (x 1)*(-Real.sin (x 1)) = 0
  linear_combination Real.sin (x 1)*Real.cos (x 1)*(Real.sin_sq_add_cos_sq (x 2))

lemma unit_tangent (x : Point) : ∑ i : Ix, sphereParam x i * phiUnit x i = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.sin (x 1)*Real.cos (x 2))*(-Real.sin (x 2)) +
    (Real.sin (x 1)*Real.sin (x 2))*Real.cos (x 2) + Real.cos (x 1)*0 = 0
  ring

lemma theta_unit (x : Point) : (∑ i : Ix, thetaFrame x i ^ 2) = 1 := by
  simp only [Fin.sum_univ_three]
  change (Real.cos (x 1)*Real.cos (x 2))^2 + (Real.cos (x 1)*Real.sin (x 2))^2 + (-Real.sin (x 1))^2 = 1
  linear_combination (Real.cos (x 1)^2)*(Real.sin_sq_add_cos_sq (x 2)) + Real.sin_sq_add_cos_sq (x 1)

lemma unit_unit (x : Point) : (∑ i : Ix, phiUnit x i ^ 2) = 1 := by
  simp only [Fin.sum_univ_three]
  change (-Real.sin (x 2))^2 + Real.cos (x 2)^2 + (0:ℝ)^2 = 1
  nlinarith [Real.sin_sq_add_cos_sq (x 2)]

lemma theta_unit_orthogonal (x : Point) : (∑ i : Ix, thetaFrame x i * phiUnit x i) = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.cos (x 1)*Real.cos (x 2))*(-Real.sin (x 2)) +
    (Real.cos (x 1)*Real.sin (x 2))*Real.cos (x 2) + (-Real.sin (x 1))*0 = 0
  ring

end
end CKSSphericalChart

end

end OAI
