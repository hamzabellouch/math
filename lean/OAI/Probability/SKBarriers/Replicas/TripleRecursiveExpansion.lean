import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Hierarchy.HierarchySandwich
import OAI.Probability.SKBarriers.Hierarchy.HierarchyScoreGeneral
import OAI.Probability.SKBarriers.Scalar.ScalarSymmetricTaylor
import OAI.Probability.SKBarriers.Scalar.UniformExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Linear
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_composition_coordinate_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hL : LipschitzWith 1 f) (X : E →L[ℝ] ℝ) (z e : E) :
    |fderiv ℝ (f ∘ X) z e| ≤ |X e| := by
  rw [fderiv_comp z (hf.1.differentiable (by norm_num) _) X.differentiableAt,
    X.fderiv,ContinuousLinearMap.comp_apply]
  have H := ((fderiv ℝ f (X z)).le_opNorm (X e)).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul] using H
end Linear

def tripleMiddleBoundary (f : ℝ → ℝ) {n : ℕ}
    (X Z : ParameterSpace n →L[ℝ] ℝ) : ParameterSpace n → ℝ :=
  fun z => f (X z)+2*f (Z z)

def tripleModifiedBoundary (f : ℝ → ℝ) {n : ℕ}
    (X Z Y : ParameterSpace n →L[ℝ] ℝ) (δ : ℝ) : ParameterSpace n → ℝ :=
  fun z => f (X z)+f (Z z+δ*Y z)+f (Z z-δ*Y z)

theorem tripleMiddleBoundary_regular {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (X Z : ParameterSpace n →L[ℝ] ℝ) : BoundedDerivs (tripleMiddleBoundary f X Z) :=
  (hf.compCLM X).add ((hf.compCLM Z).const_mul 2)

theorem tripleModifiedBoundary_regular {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (X Z Y : ParameterSpace n →L[ℝ] ℝ) (δ : ℝ) :
    BoundedDerivs (tripleModifiedBoundary f X Z Y δ) :=
  ((hf.compCLM X).add (hf.compCLM (Z+δ • Y))).add (hf.compCLM (Z-δ • Y))

theorem tripleMiddleBoundary_coordinate_bound {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hL : LipschitzWith 1 f) (X Z : ParameterSpace n →L[ℝ] ℝ) (i : Fin n) (z : ParameterSpace n) :
    |fderiv ℝ (tripleMiddleBoundary f X Z) z (coordinateAxis n i)| ≤
      |X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)| := by
  let F := f ∘ X
  let G := f ∘ Z
  have hF := (hf.compCLM X).1.differentiable (by norm_num)
  have hG := (hf.compCLM Z).1.differentiable (by norm_num)
  change |fderiv ℝ (fun z => F z+2*G z) z (coordinateAxis n i)| ≤ _
  dsimp only [F,G,Function.comp_def]
  rw [fderiv_fun_add (hF z) ((hG z).const_mul 2),fderiv_const_mul (hG z),
    add_apply,smul_apply,smul_eq_mul]
  calc
    _ ≤ |fderiv ℝ F z (coordinateAxis n i)|+|2*fderiv ℝ G z (coordinateAxis n i)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (scalar_composition_coordinate_bound hf hL X z _)
        (mul_le_mul_of_nonneg_left (scalar_composition_coordinate_bound hf hL Z z _) (by norm_num))

theorem tripleMiddle_recursive_expansion (n t : ℕ) (m : Fin n → ℝ) (p v : Fin t → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (hp : ∀ i, p i∈Icc (0:ℝ) 1) (hpmono : Monotone p)
    (X Z : ParameterSpace n →L[ℝ] ℝ) (a : Fin n → ℝ) (x : ℝ)
    {c δ : ℝ} (hc : 0<c) (hδ : 4*δ^2 ≤ c) (hδ1 : |δ| ≤ 1)
    (hsmall : c*(4*(∑ i, (a i)^2)+
      (2*∑ i, |a i| *(|X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)|))^2) ≤ 1/2) :
    let f := scalarHierarchy t p v scalarSpinTerminal
    let F := tripleMiddleBoundary f X Z
    let Y := coordinateLinear n a
    hierarchyPressure n m (tripleModifiedBoundary f X Z Y δ) x ≤
      hierarchyPressure n m F x+
      δ^2*(∫ z, rootHessian 0 f (Z z)*(Y z)^2 ∂hierarchyPathLaw n m F x)+
      ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/c^2)+32/c^2)*2)*|δ|^3 := by
  dsimp only
  let f := scalarHierarchy t p v scalarSpinTerminal
  let F := tripleMiddleBoundary f X Z
  let Y := coordinateLinear n a
  let G := tripleModifiedBoundary f X Z Y δ
  let μ := hierarchyPathLaw n m F x
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular t p v
  have hFL : LipschitzWith 1 f := scalarHierarchy_lipschitz t p v (fun i => (hp i).1)
    scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
  have hF : BoundedDerivs F := tripleMiddleBoundary_regular hf X Z
  have hG : BoundedDerivs G := tripleModifiedBoundary_regular hf X Z Y δ
  have hU : BoundedDerivs (fun z => G z-F z) := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hG.add (hF.const_mul (-1))
  let := hierarchyPathLaw_probability n m F hF x
  obtain ⟨hE,hM⟩ := hierarchy_exp_square_bound n m hm hmono F hF
    (fun i => |X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)|) (by intro i; positivity)
    (fun z i => tripleMiddleBoundary_coordinate_bound hf hFL X Z i z) x a hc.le hsmall
  have hΔ : Integrable (fun z => G z-F z) μ :=
    hU.hasExpGrowth.integrable_hierarchyPathLaw n m hF hU.1.continuous x
  have hcA : Continuous (fun z : ParameterSpace n => rootHessian 0 f (Z z)) :=
    (scalarHierarchy_spin_hessian_lipschitz t p v hp hpmono).continuous.comp Z.continuous
  have hbA (z : ParameterSpace n) : ‖rootHessian 0 f (Z z)‖ ≤ 1 := by
    have H := scalarHierarchy_spin_derivative_bounds t p v hp (Z z)
    change |fderiv ℝ (fderiv ℝ f) (Z z) 1 1| ≤ 1
    rw [abs_of_pos H.2.1]
    exact H.2.2.trans (sub_le_self _ (sq_nonneg _))
  have hA : Integrable (fun z => rootHessian 0 f (Z z)*(Y z)^2) μ :=
    ((HasExpGrowth.of_bounded zero_le_one hbA).mul ((HasExpGrowth.linear Y).pow 2)).integrable_hierarchyPathLaw
      n m hF (hcA.mul (Y.continuous.pow 2)) x
  have he (z) : G z-F z=symmetricIncrement f (Z z) (δ*Y z) := by
    dsimp [F,G,tripleMiddleBoundary,tripleModifiedBoundary,symmetricIncrement]; ring
  have H := log_integral_exp_cubic_expansion μ Y (fun z => G z-F z)
    (fun z => rootHessian 0 f (Z z)) Y.continuous.aestronglyMeasurable hΔ hA hc hδ hδ1
    (by positivity : 0 ≤ 2*(susceptibilityLipschitzConstant:ℝ)) hE hM
    (ae_of_all _ (fun z => by rw [he]; exact (scalarHierarchy_symmetricIncrement_bounds t p v hp hpmono _ δ _).1))
    (ae_of_all _ (fun z => by rw [he]; exact (scalarHierarchy_symmetricIncrement_bounds t p v hp hpmono _ δ _).2))
  have HS := (hierarchyPressure_increment_integral_sandwich n m hm hF hG x).2
  change hierarchyPressure n m G x ≤ hierarchyPressure n m F x+_+_
  linarith

end SK.Analytic

end
end

end OAI
