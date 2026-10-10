import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.NoncompactSubgradient
import OAI.Geometry.WeakHessian.LocalBounds.LocalPairing
import OAI.Geometry.WeakHessian.Entropy.FisherRoot

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile46
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_eq_square_sqrt (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) :
    densityMeasure m u = squareDensityMeasure m (fun x => Real.sqrt (u x)) := by
  apply withDensity_congr_ae
  filter_upwards [hun] with x hx
  rw [Real.sq_sqrt hx]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma QuadraticLipschitzBound.weighted_memLp (o : X) {T : ℝ} (hT : 0 ≤ T)
    {φ V : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (hzero : φ o = 0)
    (hV : Measurable V) (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    MemLp (fun x => φ x*Real.exp (-V x)) 2 m := by
  apply hW.mono ((hφ.continuous hT).aestronglyMeasurable.mul (hV.neg.exp.aestronglyMeasurable))
  apply ae_of_all
  intro x
  change |φ x*Real.exp (-V x)| ≤ |(dist x o+T)^2*Real.exp (-V x)|
  simp only [abs_mul,abs_of_nonneg (sq_nonneg (dist x o+T)),abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hφ.centered_bound hT hzero x) (Real.exp_pos _).le

lemma QuadraticLipschitzBound.cut_memLp (hfin : FiniteOnBoundedSets m) (o : X)
    {T : ℝ} (hT : 0 < T) {φ : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (n : ℕ) :
    MemLp (fun x => φ x*radialCutoff o n x) 2 m := by
  let : Nonempty X := ⟨o⟩
  exact ((hφ.localSobolev hfin hT).mul_lipschitz_compactSupport hfin
    (radialCutoff_lipschitz o n) (radialCutoff_compact o n)).1

variable [SigmaFinite m]

theorem RCD.generator_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (o : X) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m, u x ≤ B)
    (hI : Integrable (fisherDensity (m := m) u) m)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hEnt : FiniteEntropy m (μ:Measure X))
    (T : ℝ≥0) (hT : 0 < T)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
        -(∫ x,A x*φ x ∂m) := by
  let w (x : X) := Real.sqrt (u x)
  have hum := (Lp.stronglyMeasurable u).measurable
  have hw := hu.1.sqrt_of_fisher hfin hum hun hi hI
  have hwm : Measurable w := hum.sqrt
  have hwn : ∀ᵐ x ∂m, 0 ≤ w x := ae_of_all _ fun x => Real.sqrt_nonneg _
  have hwB : ∀ᵐ x ∂m, w x ≤ Real.sqrt B :=
    huB.mono fun x hx => (Real.sqrt_le_sqrt_iff hB).mpr hx
  have hwW : MemLp (fun x => w x*(dist x o+T)) 2 m := by
    apply (memLp_two_iff_integrable_sq (hwm.aestronglyMeasurable.mul
      (continuous_id.dist continuous_const |>.add continuous_const).aestronglyMeasurable)).mpr
    exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by
      change u x*(dist x o+T)^2 = (Real.sqrt (u x)*(dist x o+T))^2
      rw [mul_pow,Real.sq_sqrt hx])
  have hμw : (μ:Measure X) = squareDensityMeasure m w := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,hent⟩ := hrcd.noncompact_entropy_subdifferential hN hfin
    w hw hwm (Real.sqrt_nonneg B) hwn hwB μ ν hμw hEnt o T hT hwW hsν hCt hdν
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,?_⟩
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
  have hp := hu.quadratic_weighted_pairing hfin hpar o hV hU hA
    (show (0:ℝ)<T from hT) hφ hφW hD
  have hsq : (fun x => w x^2) =ᵐ[m] u := hun.mono fun x hx => Real.sq_sqrt hx
  have hg : gamma m u φ =ᵐ[m] (fun x => 2*w x*gamma m φ w x) := by
    filter_upwards [gamma_square_bounded hfin hpar hw (hφ.localSobolev hfin hT) (B := Real.sqrt B)
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2),
      gamma_congr_ae hsq Filter.EventuallyEq.rfl,gamma_comm (m := m) w φ] with x h1 h2 h3
    rw [← h2,h1,h3]
  rw [integral_congr_ae hg] at hp
  linarith
end WeakHessian

end
end InlinedFile46

end OAI
