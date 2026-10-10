import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropyBoundedSupported
import OAI.Geometry.WeakHessian.Entropy.EntropyContact
import OAI.Geometry.WeakHessian.Entropy.ZeroDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile4
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_restrict {m : Measure X} {w : X → ℝ} {Q : Set X}
    (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    squareDensityMeasure (m.restrict Q) w = squareDensityMeasure m w := by
  change (m.restrict Q).withDensity _ = squareDensityMeasure m w
  rw [← restrict_withDensity hQ]
  exact Measure.restrict_eq_self_of_ae_mem hs

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_support_integral {m : Measure X} {w f : X → ℝ}
    (hw : Measurable w) {Q : Set X} (hQ : MeasurableSet Q)
    (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    (∫ x, w x*f x ∂m.restrict Q) = ∫ x, w x*f x ∂m := by
  have H := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp hs
  rw [← integral_indicator hQ]
  apply integral_congr_ae
  filter_upwards [H] with x hx
  by_cases h : x ∈ Q
  · simp only [indicator_of_mem h]
  · have he : ENNReal.ofReal (w x^2) = 0 := not_not.mp (mt hx h)
    have hz : w x = 0 := by
      have H := ENNReal.ofReal_eq_zero.mp he
      nlinarith [sq_nonneg (w x)]
    simp only [indicator_of_notMem h,hz,zero_mul]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsTestPlan.entropy_squareRoot_subdifferential_original {m : Measure X} [SigmaFinite m]
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (w : X →ᵇ ℝ) {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ)
    (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h0 : interpolation π timeZero = squareDensityMeasure m w) {K : ℝ}
    (hcurv : ∀ t : Time, FiniteEntropy m (interpolation π t) ∧
      entropyReal m (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal m (interpolation π timeZero)+
          (t:ℝ)*entropyReal m (interpolation π timeOne)-
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)) :
    entropyReal m (interpolation π timeZero)-entropyReal m (interpolation π timeOne)+
      K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤
      ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure π := hπ.1
  let (t : Time) : IsProbabilityMeasure (interpolation π t) := interpolation_probability π t
  obtain ⟨o,R,hR,htracks⟩ := hb
  let Q := Metric.closedBall o R
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  have hs (t : Time) : ∀ᵐ x ∂interpolation π t, x ∈ Q := by
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hQ).mpr
    exact htracks.mono fun γ hγ => hγ t
  let n := m.restrict Q
  let : IsFiniteMeasure n := ⟨by
    simpa only [n,Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have he (t : Time) : entropyReal n (interpolation π t) = entropyReal m (interpolation π t) :=
    entropyReal_restrict_reference hQ (hcurv t).1.1 (hs t)
  simp only [n] at he
  have h0s : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q := by rw [← h0]; exact hs timeZero
  have h0n : interpolation π timeZero = squareDensityMeasure n w := by
    rw [h0,show squareDensityMeasure n w = squareDensityMeasure m w from squareDensity_restrict hQ h0s]
  have H := hπ.entropy_squareRoot_subdifferential hfin hpar ⟨o,R,hR,htracks⟩ hgeo
    (Measure.restrict_le_self.absolutelyContinuous : n ≪ m) w hφ hw hwn hdual hcontact h0n
    (K := K) (fun t => ⟨(finiteEntropy_restrict_reference_iff hQ (hs t)).mpr (hcurv t).1, by
      simp only [he]; exact (hcurv t).2⟩)
  simp only [he] at H
  have hi := squareDensity_support_integral (f := fun x => 2*gamma m φ w x) hw.continuous.measurable hQ h0s
  simp only [mul_left_comm (w _) 2] at hi
  have hire : (∫ x, 2*w x*gamma m φ w x ∂n) = ∫ x, 2*w x*gamma m φ w x ∂m := by
    convert hi using 1 <;> congr 1 <;> funext x <;> ring
  simp only [n] at hire
  rwa [hire] at H

variable [SecondCountableTopology X] [ProperSpace X]

theorem RCD.bounded_entropy_subdifferential {m : Measure X} [SigmaFinite m] {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X →ᵇ ℝ) {T : ℝ≥0} (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hdμ : (μ:Measure X) ≤ C • m) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      LipschitzWith (2*R) φ ∧ LipschitzWith (2*R) ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+
        K/2*planEnergy (π:Measure (Curve X)) ≤ ∫ x,2*w x*gamma m φ w x ∂m := by
  obtain ⟨π,hπ,hb,hgeo,hopt,hent,hchord,hcomp⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ ν o R hsμ hsν hC0 hCt hdμ hdν
  obtain ⟨φ,ψ,hφ,hψ,hdual,hcontact⟩ :=
    WeakHessianTransport.bounded_support_kantorovich_potentials
      (isCompact_closedBall o R) (Metric.nonempty_closedBall.mpr R.coe_nonneg)
      (μ:Measure X) (ν:Measure X) (ae_iff.mpr hsμ) (ae_iff.mpr hsν) hopt
      (R := 2*R) (by
        intro x hx y hy
        have H := dist_triangle x o y
        rw [dist_comm o y] at H
        change dist x o ≤ R at hx
        change dist y o ≤ R at hy
        push_cast
        linarith)
  have hc : ∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := by
    apply (ae_map_iff ((continuous_eval_const timeZero).prodMk (continuous_eval_const timeOne)).measurable.aemeasurable ?_).mp hcontact
    exact (isClosed_eq ((hφ.continuous.comp continuous_fst).add (hψ.continuous.comp continuous_snd))
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet
  obtain ⟨h0,h1⟩ := hopt.1.interpolation_endpoints
  refine ⟨π,φ,ψ,hπ,hb,hgeo,hopt,hφ,hψ,hdual,hc,?_⟩
  have H := hπ.entropy_squareRoot_subdifferential_original hfin
    (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hb hgeo w hφ hw hwn hdual hc
    (h0.trans hμ) (K := K) (fun t => ⟨hent t,by simpa only [h0,h1,planEnergy] using hchord t⟩)
  simpa only [h0,h1,planEnergy] using H

end WeakHessian

end
end InlinedFile4

end OAI
