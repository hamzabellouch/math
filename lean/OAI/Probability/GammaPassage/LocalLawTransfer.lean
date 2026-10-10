import OAI.Probability.GammaPassage.LocalCenteredConcentration
import OAI.Probability.GammaPassage.FiniteMoments

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.local_restriction_law
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ) :
    P.map (fun ω (e : ↥(FiniteLocal.localEdges p q R)) => τ e ω) =
      finiteGammaMeasure (ι := ↥(FiniteLocal.localEdges p q R)) shape rate :=
  h.finiteJointLaw (FiniteLocal.localEdges p q R)

/-- The local passage-time law is the pushforward of the finite Gamma product law. -/
theorem GammaEnvironment.localPassageTime_law
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    P.map (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) =
      (finiteGammaMeasure shape rate).map (FiniteLocal.finitePassageTime p q R) := by
  rw [← h.local_restriction_law p q R,
    Measure.map_map (FiniteLocal.measurable_finitePassageTime p q R hR)
      (Measurable.of_eval (fun e => h.measurable e))]
  congr 1
  funext ω
  exact (FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)).symm

/-- The finite-coordinate passage time has the same expectation as its realization
in a Gamma environment. -/
theorem GammaEnvironment.integral_localPassageTime
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) =
      ∫ v, FiniteLocal.finitePassageTime p q R v ∂finiteGammaMeasure shape rate := by
  have hi := h.integral_finiteJoint (FiniteLocal.localEdges p q R)
    (FiniteLocal.finitePassageTime p q R)
    (FiniteLocal.measurable_finitePassageTime p q R hR)
  have hF : (fun ω => FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) =
      (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) := by
    funext ω
    exact FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)
  change (∫ ω, FiniteLocal.finitePassageTime p q R
    (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) ∂P) = _ at hi
  rw [hF] at hi
  exact hi

/-- Local passage times in a Gamma environment are integrable. -/
theorem GammaEnvironment.integrable_localPassageTime
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    Integrable (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) P := by
  have hpos : ∀ᵐ v ∂finiteGammaMeasure (ι := ↥(FiniteLocal.localEdges p q R)) shape rate,
      0 ≤ FiniteLocal.finitePassageTime p q R v :=
    (finiteGammaMeasure_ae_nonneg hs hr).mono fun v hv =>
      FiniteLocal.finitePassageTime_nonneg p q R hR v hv
  have hi := (hasDerivAt_integral_exp_zero
    (FiniteLocal.measurable_finitePassageTime p q R hR) hpos
    (show 0 < rate/2 by positivity)
    (FiniteLocal.integrable_finitePassageTime_exp hs hr p q R hR (rate/2) le_rfl)).1
  rw [← h.local_restriction_law p q R] at hi
  have hc := hi.comp_measurable (Measurable.of_eval (fun e => h.measurable e))
  have hF : (fun ω => FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) =
      (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) := by
    funext ω
    exact FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)
  change Integrable (fun ω => FiniteLocal.finitePassageTime p q R
    (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) P at hc
  rw [hF] at hc
  exact hc

/-- Centered local passage times have exponential tails at scale `sqrt R`,
for every real threshold. -/
theorem GammaEnvironment.localPassageTime_centered_exponential
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (t : ℝ) :
    P {ω | t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ η, FiniteLocal.passageTime (fun e => τ e η) p q R ∂P|} ≤
      2*ENNReal.ofReal (exp (1-FiniteLocal.concentrationKappa shape rate*t)) := by
  rw [h.integral_localPassageTime p q R hR]
  let A : Set (FiniteLocal.Coordinates p q R) :=
    {v | t*sqrt R ≤ |FiniteLocal.finitePassageTime p q R v -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      ((FiniteLocal.measurable_finitePassageTime p q R hR).sub measurable_const))
  have hm := Measure.map_apply (μ := P)
    (Measurable.of_eval (fun e : ↥(FiniteLocal.localEdges p q R) => h.measurable e)) hA
  rw [h.local_restriction_law p q R] at hm
  have he : P {ω | t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|} =
      (finiteGammaMeasure shape rate) A := by
    rw [hm]
    congr 1
    ext ω
    change (t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|) ↔
      (t*sqrt R ≤ |FiniteLocal.finitePassageTime p q R
        (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|)
    rw [show FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) =
        FiniteLocal.passageTime (fun e => τ e ω) p q R from
      FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)]
  rw [he]
  exact FiniteLocal.finitePassageTime_centered_exponential hs hr p q R hR t

end GammaFPP

end OAI
