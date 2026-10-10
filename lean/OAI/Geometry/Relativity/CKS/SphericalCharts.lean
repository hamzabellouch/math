import OAI.Geometry.Relativity.CKS.InducedSphereCalculus

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

def sphereParam (x : Point) : E := WithLp.toLp 2
  ![Real.sin (x 1)*Real.cos (x 2), Real.sin (x 1)*Real.sin (x 2), Real.cos (x 1)]
def thetaFrame (x : Point) : E := WithLp.toLp 2
  ![Real.cos (x 1)*Real.cos (x 2), Real.cos (x 1)*Real.sin (x 2), -Real.sin (x 1)]
def phiUnit (x : Point) : E := WithLp.toLp 2 ![-Real.sin (x 2), Real.cos (x 2), 0]
def phiFrame (x : Point) : E := Real.sin (x 1) • phiUnit x

def chartVector (i : Ix) (x : Point) : E := ![0,thetaFrame x,phiFrame x] i

lemma sphereParam_smooth : ContDiff ℝ ∞ sphereParam := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [sphereParam] <;> fun_prop
lemma thetaFrame_smooth : ContDiff ℝ ∞ thetaFrame := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [thetaFrame] <;> fun_prop
lemma phiUnit_smooth : ContDiff ℝ ∞ phiUnit := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [phiUnit] <;> fun_prop
lemma phiFrame_smooth : ContDiff ℝ ∞ phiFrame := by
  unfold phiFrame
  exact ((coord 1).contDiff.sin).smul phiUnit_smooth
lemma chartVector_smooth (i : Ix) : ContDiff ℝ ∞ (chartVector i) := by
  fin_cases i
  · exact contDiff_const
  · exact thetaFrame_smooth
  · exact phiFrame_smooth

lemma sphereParam_norm (x : Point) : ‖sphereParam x‖ = 1 := by
  have h := EuclideanSpace.norm_sq_eq (sphereParam x)
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three] at h
  change ‖sphereParam x‖^2 = (Real.sin (x 1)*Real.cos (x 2))^2 +
    (Real.sin (x 1)*Real.sin (x 2))^2 + Real.cos (x 1)^2 at h
  have h₂ := congrArg (fun z : ℝ => Real.sin (x 1)^2*z)
    (Real.sin_sq_add_cos_sq (x 2))
  nlinarith [Real.sin_sq_add_cos_sq (x 1), norm_nonneg (sphereParam x)]

lemma component_fderiv {f : Point → E} {x : Point} (hf : DifferentiableAt ℝ f x)
    (v : Point) (i : Ix) :
    (fderiv ℝ f x v) i = D v (fun y => f y i) x := by
  have h := ((EuclideanSpace.proj i).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact (congrArg (fun L : Point →L[ℝ] ℝ => L v) h).symm

lemma fderiv_sphereParam (x : Point) (i : Ix) :
    fderiv ℝ sphereParam x (basis i) = chartVector i x := by
  ext j
  rw [component_fderiv (sphereParam_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 :=
    D_coord a b x
  fin_cases i <;> fin_cases j <;>
    dsimp [sphereParam, chartVector, thetaFrame, phiFrame, phiUnit]
  all_goals
    simp only [D_mul _ hd1.sin hd2.cos, D_mul _ hd1.sin hd2.sin,
      D_sin _ hd1, D_sin _ hd2, D_cos _ hd1, D_cos _ hd2, dc, Fin.reduceEq, ite_false, ite_true]
    norm_num
    <;> ring

lemma angular_chain {F : E → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F (sphereParam x)) (i : Ix) :
    D (basis i) (fun y => F (sphereParam y)) x =
      ∑ k : Ix, chartVector i x k * grad F (sphereParam x) k := by
  unfold D
  change fderiv ℝ (F ∘ sphereParam) x (basis i) = _
  rw [fderiv_comp x hF (sphereParam_smooth.differentiable (by simp) x)]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ sphereParam x (basis i)) = _
  rw [fderiv_sphereParam, CKSInducedSphere.fderiv_expand]

end
end CKSSphericalChart

end

end OAI
