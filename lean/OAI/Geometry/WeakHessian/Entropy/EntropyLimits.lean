import Mathlib
import OAI.Geometry.WeakHessian.Calculus.RnDerivRestrictReference
import OAI.Geometry.WeakHessian.Entropy.EntropyRealContinuousSupport
import OAI.Geometry.WeakHessian.Entropy.ZeroDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile11
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]

lemma entropyReal_le_of_tendsto_supported (hfin : FiniteOnBoundedSets m)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (o : X) (R : ℝ≥0)
    (hss : ∀ n, ∀ᵐ x ∂(μs n:Measure X), x ∈ Metric.closedBall o R)
    (hs : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o R)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hds : ∀ n, (μs n:Measure X) ≤ C • m) (hd : (μ:Measure X) ≤ C • m)
    {a : ℕ → ℝ} {A : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hE : ∀ n, entropyReal m (μs n:Measure X) ≤ a n) : entropyReal m (μ:Measure X) ≤ A := by
  let Q := Metric.closedBall o (R:ℝ)
  have hQ : MeasurableSet Q := measurableSet_closedBall
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have dom (ν : ProbabilityMeasure X) (hsν : ∀ᵐ x ∂(ν:Measure X), x ∈ Q)
      (hdν : (ν:Measure X) ≤ C • m) : (ν:Measure X) ≤ C • m.restrict Q := by
    have H := Measure.restrict_mono_measure hdν Q
    rwa [Measure.restrict_eq_self_of_ae_mem hsν,Measure.restrict_smul] at H
  have ac (ν : ProbabilityMeasure X) (hdν : (ν:Measure X) ≤ C • m) : (ν:Measure X) ≪ m :=
    hdν.absolutelyContinuous.trans (Measure.AbsolutelyContinuous.rfl.smul_left _)
  rw [← entropyReal_restrict_reference hQ (ac μ hd) hs]
  apply (entropyReal_le_iff_continuous_support hC (dom μ hs hd)).mpr
  intro g
  have H : Tendsto (fun n => (∫ x,g x ∂(μs n:Measure X))-(∫ x,Real.exp (g x) ∂m.restrict Q)+1)
      atTop (𝓝 ((∫ x,g x ∂(μ:Measure X))-(∫ x,Real.exp (g x) ∂m.restrict Q)+1)) :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).tendsto μ |>.comp hμ).sub_const _ |>.add_const 1
  have J := le_of_tendsto_of_tendsto' H ha (fun n => by
    have HF := entropyReal_fenchel (finiteEntropy_of_bounded_density hC (dom (μs n) (hss n) (hds n))) g
    rw [entropyReal_restrict_reference hQ (ac (μs n) (hds n)) (hss n)] at HF
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using HF.trans (hE n))
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using J

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SigmaFinite m] in
lemma squareDensity_le_of_bound {w : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B) :
    squareDensityMeasure m w ≤ ENNReal.ofReal (B^2) • m := by
  rw [squareDensityMeasure,← withDensity_const]
  apply withDensity_mono
  filter_upwards [hwn,hwB] with x hx hy
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ hx hB).mpr hy)

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SigmaFinite m] in
lemma squareDensity_ae_support {w : X → ℝ} (hw : Measurable w) {Q : Set X}
    (hzero : ∀ᵐ x ∂m, x ∉ Q → w x = 0) :
    ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q := by
  apply (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mpr
  filter_upwards [hzero] with x hx hn
  by_contra h
  exact hn (by rw [hx h]; simp)
end WeakHessian

end
end InlinedFile11

end OAI
