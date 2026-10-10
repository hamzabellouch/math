import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatEnergyQuotient
import OAI.Geometry.WeakHessian.HeatFlow.HeatFormContinuous
import OAI.Geometry.WeakHessian.Calculus.RightEndpointDerivative

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile108
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_pairing_deriv_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u q : Lp ℝ 2 m}
    (hu : Sobolev m (u : X → ℝ)) (hq : Sobolev m (q : X → ℝ)) :
    HasDerivWithinAt (fun t => ⟪q,cheegerHeat h t u⟫_ℝ)
      (-(∫ x,gamma m (u : X → ℝ) q x ∂m)) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_right_deriv
    (d := fun t => -(∫ x,gamma m (cheegerHeat h t u) q x ∂m))
  · exact continuousOn_const.inner (cheegerHeat_continuousOn hfin h u)
  · intro t ht
    obtain ⟨A,hA⟩ := (cheeger_closedQuadraticEnergy h).heat_hasFormGenerator m ht u
    change (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A at hA
    have hd := cheegerHeat_deriv_right_of_generator hfin h ht.le hA
    have HH := (hasDerivWithinAt_const t (Ici t) q).inner ℝ hd
    simp only [inner_zero_left,add_zero] at HH
    have hqe := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp q)).mp hq
    have hpair := hA.2 ⟨q,hqe⟩
    rw [← hcd.global_integral_gamma_form hfin o h ⟨cheegerHeat h t u,hA.1⟩ ⟨q,hqe⟩] at hpair
    have he : ⟪q,A⟫_ℝ = -(∫ x,gamma m (cheegerHeat h t u) q x ∂m) := by
      rw [real_inner_comm]
      linarith
    rwa [he] at HH
  · exact (hcd.cheegerHeat_integral_gamma_zero hfin h o hu hq).neg
end WeakHessian

end
end InlinedFile108

end OAI
