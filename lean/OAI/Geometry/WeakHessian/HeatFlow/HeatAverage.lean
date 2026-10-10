import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile116
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_integral_formGenerator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator
      (∫ s in 0..t,cheegerHeat h s u) (cheegerHeat h t u-u) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := Q.resolventLinear
  have hi (v : Lp ℝ 2 m) : IntervalIntegrable (fun s => cheegerHeat h s v) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h v).mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  have he : ∀ s,cheegerHeat h s (R u) = R (cheegerHeat h s u) :=
    fun s => realHeat_resolvent m Q.resolvent_positive s u
  have H := cheegerHeat_integral_generator hfin h (Q.isFormGenerator_resolvent u) ht
  change (∫ s in 0..t,cheegerHeat h s (R u-u)) = cheegerHeat h t (R u)-R u at H
  simp_rw [map_sub,he] at H
  rw [intervalIntegral.integral_sub ⟨R.integrable_comp (hi u).1,R.integrable_comp (hi u).2⟩ (hi u),
    R.intervalIntegral_comp_comm (hi u)] at H
  apply (Q.isFormGenerator_iff _ _).mpr
  change R ((∫ s in 0..t,cheegerHeat h s u)-(cheegerHeat h t u-u)) = _
  rw [map_sub,map_sub]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp H).trans (add_comm _ _))

lemma cheegerHeat_average_formGenerator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator
      (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u) (t⁻¹ • (cheegerHeat h t u-u)) :=
  (cheeger_closedQuadraticEnergy h).formGenerator_smul _ (cheegerHeat_integral_formGenerator hfin h u ht)
end WeakHessian

end
end InlinedFile116

end OAI
