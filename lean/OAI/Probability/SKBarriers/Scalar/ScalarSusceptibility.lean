import Mathlib
import OAI.Probability.SKBarriers.Scalar.DerivativeStability
import OAI.Probability.SKBarriers.Hierarchy.RootSusceptibility

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpinRoot_curvature (n : ℕ) (v : Fin n → ℝ) :
    RootSpinCurvature n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v)) := by
  intro z
  have hL : scalarSpinField n v (parameterAxis n)=1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  have H := affineLogPartition_bool_curvature (scalarSpinField n v) z (parameterAxis n) hL
  exact ⟨H.1,H.2.le⟩

theorem scalarSpinRoot_curvature_eq (n : ℕ) (v : Fin n → ℝ) (z : ParameterSpace n) :
    rootHessian n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v)) z =
      1-(rootGradient n (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) z)^2 := by
  have hL : scalarSpinField n v (parameterAxis n)=1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  exact (affineLogPartition_bool_curvature (scalarSpinField n v) z (parameterAxis n) hL).2

theorem scalarHierarchy_spin_hasDerivAt (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (scalarHierarchy n m v scalarSpinTerminal)
      (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x) x := by
  exact (scalarHierarchy_spin_regular n m v).1.differentiable (by norm_num) x |>.hasDerivAt

theorem scalarHierarchy_spin_gradient_hasDerivAt (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal))
      (rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x) x := by
  simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
    rootGradientLine_hasDerivAt 0 (scalarHierarchy_spin_regular n m v) 0 x

theorem scalarHierarchy_spin_gradient_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) :
    LipschitzWith 1 (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarHierarchy_spin_gradient_hasDerivAt n m v x).differentiableAt)
  intro x
  rw [(scalarHierarchy_spin_gradient_hasDerivAt n m v x).deriv]
  have H := scalarHierarchy_spin_derivative_bounds n m v hm x
  have h : |rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x|≤1 := by
    change |fderiv ℝ (fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal)) x 1 1|≤1
    rw [abs_of_pos H.2.1]
    linarith [H.2.2,sq_nonneg (fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal) x 1)]
  exact_mod_cast h

theorem scalarHierarchy_spin_hessian_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m) :
    LipschitzWith susceptibilityLipschitzConstant
      (rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal)) := by
  rw [scalarHierarchy_spin_eq]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := hierarchyPressure_rootHessian_shift_bound n m hm hmono
    (affineLogPartition_boundedDerivs _ _) (scalarSpinRoot_curvature n v)
    (scalarSpinRoot_curvature_eq n v) y (x-y)
  simpa only [add_sub_cancel,Real.dist_eq] using H

theorem scalarHierarchy_gradient_stability {n l : ℕ} (m v : Fin n → ℝ)
    (a w : Fin l → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) {ε : ℝ}
    (hε : ∀ x, |scalarHierarchy n m v scalarSpinTerminal x-
      scalarHierarchy l a w scalarSpinTerminal x|≤ε) (x h : ℝ) (hh : 0<h) :
    |rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x-
      rootGradient 0 (scalarHierarchy l a w scalarSpinTerminal) x|≤2*ε/h+2*h := by
  have HL := (scalarHierarchy_spin_gradient_lipschitz n m v hm).sub
    (scalarHierarchy_spin_gradient_lipschitz l a w ha)
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (1+1) ε
    (fun z => (scalarHierarchy_spin_hasDerivAt n m v z).sub
      (scalarHierarchy_spin_hasDerivAt l a w z)) HL hε x h hh
  norm_num at H
  exact H

theorem scalarHierarchy_hessian_stability {n l : ℕ} (m v : Fin n → ℝ)
    (a w : Fin l → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hmono : Monotone m) (hamono : Monotone a)
    {ε : ℝ} (hε : ∀ x, |rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x-
      rootGradient 0 (scalarHierarchy l a w scalarSpinTerminal) x|≤ε) (x h : ℝ) (hh : 0<h) :
    |rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x-
      rootHessian 0 (scalarHierarchy l a w scalarSpinTerminal) x|≤
      2*ε/h+2*(susceptibilityLipschitzConstant:ℝ)*h := by
  have HL := (scalarHierarchy_spin_hessian_lipschitz n m v hm hmono).sub
    (scalarHierarchy_spin_hessian_lipschitz l a w ha hamono)
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _
    (susceptibilityLipschitzConstant+susceptibilityLipschitzConstant) ε
    (fun z => (scalarHierarchy_spin_gradient_hasDerivAt n m v z).sub
      (scalarHierarchy_spin_gradient_hasDerivAt l a w z)) HL hε x h hh
  simpa only [NNReal.coe_add,two_mul] using H

end SK.Analytic

end
end

end OAI
