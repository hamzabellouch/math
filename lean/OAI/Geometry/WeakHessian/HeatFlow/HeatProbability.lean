import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatMassNonneg

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile75
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma densityMeasure_probability_integral (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) : IsProbabilityMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hm) hun,hm,ENNReal.ofReal_one]

def integrableDensityProbability (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) : ProbabilityMeasure X :=
  ⟨densityMeasure m u,densityMeasure_probability_integral u hun hm⟩

omit [MetricSpace X] [BorelSpace X] in
lemma integral_densityMeasure_L2 (u f : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    (∫ x,f x ∂densityMeasure m u) = ⟪f,u⟫_ℝ := by
  rw [integral_densityMeasure,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  exact hun

omit [BorelSpace X] in
lemma cheegerHeat_density_duality (h : QuadraticCheegerEnergy m) (u f : Lp ℝ 2 m)
    {t : ℝ} (ht : 0 ≤ t) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    (∫ x,f x ∂densityMeasure m (cheegerHeat h t u)) = ⟪cheegerHeat h t f,u⟫_ℝ := by
  rw [integral_densityMeasure_L2 _ _ (cheegerHeat_nonneg h ht u hun)]
  exact ((cheegerHeat_symmetric h t) f u).symm

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

def CurvatureDimension.heatProbability {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) (t : ℝ) : ProbabilityMeasure X :=
  integrableDensityProbability (cheegerHeat h (max t 0) u)
    (cheegerHeat_nonneg h (le_max_right _ _) u hun)
    ((hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun (integrable_of_integral_eq_one hm) (le_max_right _ _)).2.trans hm)

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.heatProbability_coe {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) {t : ℝ} (ht : 0 ≤ t) :
    (hcd.heatProbability hN hfull hfin o h u hun hm t:Measure X) = densityMeasure m (cheegerHeat h t u) := by
  simp only [heatProbability,integrableDensityProbability,max_eq_left ht]
  rfl
end WeakHessian

end
end InlinedFile75

end OAI
