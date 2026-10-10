import Mathlib
import OAI.Geometry.WeakHessian.Entropy.ReducedEntropy
import OAI.Geometry.WeakHessian.HeatFlow.GeneratorSubgradient
import OAI.Geometry.WeakHessian.Measure.GeneralCostSupport

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile48
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

def quadraticWassersteinSq (μ ν : Measure X) : ℝ :=
  (⨅ q : Measure (X×X), ⨅ _ : IsCoupling q μ ν, QuadraticTransportCost q).toReal

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsOptimalCoupling.quadraticWassersteinSq_eq {μ ν : Measure X} {q : Measure (X×X)}
    (hq : IsOptimalCoupling q μ ν) : quadraticWassersteinSq μ ν = (QuadraticTransportCost q).toReal := by
  unfold quadraticWassersteinSq
  congr 1
  exact le_antisymm (iInf_le_of_le q (iInf_le _ hq.1))
    (le_iInf fun q' => le_iInf fun hq' => hq.2 q' hq')

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_sqrt_memLp (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) :
    MemLp (fun x => Real.sqrt (u x)) 2 m := by
  apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable u |>.measurable.sqrt.aestronglyMeasurable)).mpr
  exact hi.congr (hun.mono fun x hx => (Real.sq_sqrt hx).symm)

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_sqrt_weighted (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {W V : X → ℝ} (hWm : AEStronglyMeasurable W m)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => W x^2*Real.exp (-V x)) 2 m) :
    MemLp (fun x => Real.sqrt (u x)*W x) 2 m := by
  apply (memLp_two_iff_integrable_sq ((Lp.stronglyMeasurable u |>.measurable.sqrt.aestronglyMeasurable).mul hWm)).mpr
  exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by simp only [Pi.mul_apply,mul_pow,Real.sq_sqrt hx])

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_finiteEntropy [SigmaFinite m] (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    [IsFiniteMeasure (densityMeasure m u)] {V : X → ℝ}
    (hUV : Integrable (fun x => u x*V x) m) (hV : Integrable (fun x => Real.exp (-V x)) m) :
    FiniteEntropy m (densityMeasure m u) := by
  have he := densityMeasure_eq_square_sqrt u hun
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_finiteEntropy_iff (Lp.stronglyMeasurable u |>.measurable.sqrt)]
  have H := (integrable_reducedEntropy (Lp.memLp u) hun hUV hV).add hi
  apply H.congr
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,Pi.add_apply,reducedEntropy]
  ring

variable [SigmaFinite m]

lemma CurvatureDimension.density_cost_support {K N : ℝ} (hcd : CurvatureDimension m K N)
    (o : X) (T : ℝ≥0) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) := by
  exact hcd.noncompact_cost_support _ (densityMeasure_sqrt_memLp u hun hi)
    (Lp.stronglyMeasurable u |>.measurable.sqrt) μ ν (hμ.trans (densityMeasure_eq_square_sqrt u hun)) hn o T
    (densityMeasure_sqrt_weighted u hun (by fun_prop) hU hW) hsν

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [SigmaFinite m] in
lemma densityMeasure_quadratic_integrable (o : X) (T : ℝ≥0) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {V : X → ℝ}
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Integrable (fun x => (dist x o+T)^2) (densityMeasure m u) := by
  rw [densityMeasure_eq_square_sqrt u hun]
  apply (squareDensity_integrable (Lp.stronglyMeasurable u |>.measurable.sqrt)).mpr
  exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by simp only [Real.sq_sqrt hx])
end WeakHessian

end
end InlinedFile48

end OAI
