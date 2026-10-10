import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleRetained

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tripleRetained_base_pressure (n : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState) (f : ℝ → ℝ) :
    vectorHierarchy n m v (fun x => f x.1.1+2*f x.2) 0=
      hierarchyPressure n m (tripleMiddleBoundary f (coordinateLinear n (fun i => (v i).1.1))
        (coordinateLinear n (fun i => (v i).2))) 0 := by
  have H := congrFun (hierarchyPressure_vector_linear n m v (fun x : TripleRetainedState => f x.1.1+2*f x.2)
    (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  exact H.symm

theorem tripleRetained_quadratic_average (n t : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (p b : Fin t → ℝ) (hp : ∀ i,p i∈Icc (0:ℝ) 1) (hpmono : Monotone p) :
    let f := scalarHierarchy t p b scalarSpinTerminal
    vectorHierarchyAverage n m v (fun x => f x.1.1+2*f x.2)
      (fun x => rootHessian 0 f x.2*x.1.2^2) 0=
      ∫ z, rootHessian 0 f (coordinateLinear n (fun i => (v i).2) z)*
        (coordinateLinear n (fun i => (v i).1.2) z)^2
        ∂hierarchyPathLaw n m (tripleMiddleBoundary f (coordinateLinear n (fun i => (v i).1.1))
          (coordinateLinear n (fun i => (v i).2))) 0 := by
  dsimp only
  let f := scalarHierarchy t p b scalarSpinTerminal
  let X := coordinateLinear n (fun i => (v i).1.1)
  let Z := coordinateLinear n (fun i => (v i).2)
  let Y := coordinateLinear n (fun i => (v i).1.2)
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular t p b
  have hF : BoundedDerivs (tripleMiddleBoundary f X Z) := tripleMiddleBoundary_regular hf X Z
  have hc : Continuous (fun z => rootHessian 0 f (Z z)) :=
    (scalarHierarchy_spin_hessian_lipschitz t p b hp hpmono).continuous.comp Z.continuous
  have hbnd : ∀ z, ‖rootHessian 0 f (Z z)‖≤1 := by
    intro z
    have H := scalarHierarchy_spin_derivative_bounds t p b hp (Z z)
    change |fderiv ℝ (fderiv ℝ f) (Z z) 1 1|≤1
    rw [abs_of_pos H.2.1]
    exact H.2.2.trans (sub_le_self _ (sq_nonneg _))
  have he : HasExpGrowth (fun z => rootHessian 0 f (Z z)*(Y z)^2) :=
    (HasExpGrowth.of_bounded zero_le_one hbnd).mul ((HasExpGrowth.linear Y).pow 2)
  have H := congrFun (hierarchyAverage_vector_linear n m v (fun x : TripleRetainedState => f x.1.1+2*f x.2)
    (fun x => rootHessian 0 f x.2*x.1.2^2) (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ hF _ (hc.mul (Y.continuous.pow 2)) he 0

theorem tripleRetained_expansion (n t : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (p b : Fin t → ℝ) (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (hp : ∀ i,p i∈Icc (0:ℝ) 1) (hpmono : Monotone p)
    {c δ : ℝ} (hc : 0<c) (hδ : 4*δ^2≤c) (hδ1 : |δ|≤1)
    (hsmall : c*(4*(∑ i,((v i).1.2)^2)+
      (2*∑ i, |(v i).1.2| *(|(v i).1.1|+2*|(v i).2|))^2)≤1/2) :
    let f := scalarHierarchy t p b scalarSpinTerminal
    vectorHierarchy n m (fun i => tripleRetainedEmbedding δ (v i))
      (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2)) 0≤
      vectorHierarchy n m v (fun x => f x.1.1+2*f x.2) 0+
      δ^2*vectorHierarchyAverage n m v (fun x => f x.1.1+2*f x.2)
        (fun x => rootHessian 0 f x.2*x.1.2^2) 0+
      ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/c^2)+32/c^2)*2)*|δ|^3 := by
  dsimp only
  rw [tripleRetained_pressure,tripleRetained_base_pressure,tripleRetained_quadratic_average n t m v p b hp hpmono]
  apply tripleMiddle_recursive_expansion n t m p b hm hmono hp hpmono _ _ _ 0 hc hδ hδ1
  simpa only [coordinateLinear_coordinateAxis] using hsmall

end SK.Analytic

end
end

end OAI
