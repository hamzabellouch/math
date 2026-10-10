import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSpinRecursion
import OAI.Probability.SKBarriers.SpinGlass.SpinHessianFormula
import OAI.Probability.SKBarriers.Hierarchy.RootTranslation
import OAI.Probability.SKBarriers.Scalar.TerminalPathIntegral

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootPair_translate (n : ℕ) (m : Fin n → ℝ) (t : ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    rootPair n m (rootTranslate n t f) z=rootPair n m f (t • parameterAxis n+z) := by
  rw [rootPair,rootGradient_translate,hierarchyPenalty_rootTranslate,rootGradient_translate]
  rfl

theorem RootSpinCurvature.hierarchyPressure {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (hf : BoundedDerivs f) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) : RootSpinCurvature 0 (hierarchyPressure n m f) :=
  hierarchy_spin_curvature n m f hf hm h

theorem hierarchyPressure_rootHessian_shift_modulus (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x t : ℝ) :
    |rootHessian 0 (hierarchyPressure n m f) (x+t)-
      rootHessian 0 (hierarchyPressure n m f) x|≤2*|t|+2*(Real.exp (2*|t|)-1) := by
  have hfT := rootTranslate_regular n t hf
  have hT := h.translate t
  have heT (z) : rootHessian n (rootTranslate n t f) z=
      1-(rootGradient n (rootTranslate n t f) z)^2 := by
    rw [rootHessian_translate,rootGradient_translate]
    exact he _
  have hfg (z) : |rootTranslate n t f z-f z|≤|t| := by
    simpa only [rootTranslate,add_comm] using rootShift_value_bound n hf h z t
  have hpair (z) : |rootPair n m (rootTranslate n t f) z-rootPair n m f z|≤2*|t| := by
    rw [rootPair_translate]
    simpa only [add_comm] using rootPair_shift_bound n m hm hmono hf h z t
  have HT := hierarchyPressure_rootHessian_spin_formula n m hm hmono hfT hT heT x
  rw [hierarchyPressure_rootTranslate,rootHessian_translate] at HT
  simp only [parameterAxis,smul_eq_mul,mul_one] at HT
  rw [add_comm t x] at HT
  rw [HT,hierarchyPressure_rootHessian_spin_formula n m hm hmono hf h he x]
  have H := hierarchyPathLaw_observable_stability n m hm hmono hfT hf (abs_nonneg t) hfg
    (rootPair_continuous n m hfT) (rootPair_continuous n m hf) zero_le_one
    (rootPair_bound n m hm hmono hfT hT) (rootPair_bound n m hm hmono hf h) hpair x
  simpa only [sub_sub_sub_cancel_left,abs_sub_comm,mul_one] using H

theorem exp_two_mul_sub_one_bound {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    Real.exp (2*a)-1≤2*Real.exp 2*a := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z (hz : z ∈ Icc (0:ℝ) 2) => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_exp.mpr hz.2)
    (convex_Icc (0:ℝ) 2)
    (show (0:ℝ) ∈ Icc (0:ℝ) 2 by constructor <;> norm_num)
    (show 2*a ∈ Icc (0:ℝ) 2 by constructor <;> linarith [ha.1,ha.2])
  simp only [Real.norm_eq_abs,Real.exp_zero,sub_zero,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ha.1)] at H
  have hi := (le_abs_self (Real.exp (2*a)-1)).trans H
  nlinarith

def susceptibilityLipschitzConstant : ℝ≥0 := ⟨2+4*Real.exp 2,by positivity⟩

theorem hierarchyPressure_rootHessian_shift_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x t : ℝ) :
    |rootHessian 0 (hierarchyPressure n m f) (x+t)-
      rootHessian 0 (hierarchyPressure n m f) x|≤(susceptibilityLipschitzConstant:ℝ)*|t| := by
  change _≤(2+4*Real.exp 2)*|t|
  by_cases ht : |t|≤1
  · have hE := exp_two_mul_sub_one_bound ⟨abs_nonneg t,ht⟩
    have H := hierarchyPressure_rootHessian_shift_modulus n m hm hmono hf h he x t
    nlinarith
  · have hC := h.hierarchyPressure hf m hm
    have H : |rootHessian 0 (hierarchyPressure n m f) (x+t)-
        rootHessian 0 (hierarchyPressure n m f) x|≤2 :=
      (abs_sub _ _).trans (by linarith [(hC.bounds (x+t)).2,(hC.bounds x).2])
    have ht' : 1 < |t| := lt_of_not_ge ht
    have hE := Real.exp_pos (2:ℝ)
    nlinarith [mul_nonneg hE.le (abs_nonneg t)]

end SK.Analytic

end
end

end OAI
