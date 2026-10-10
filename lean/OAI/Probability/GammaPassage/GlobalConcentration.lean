import OAI.Probability.GammaPassage.GlobalCenteredConcentration
import OAI.Probability.GammaPassage.LocalMeanGap

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real

noncomputable def localizationErrorBound (shape rate : ℝ) (d R : ℕ) : ℝ :=
  (1/2 : ℝ)^R + 2*exp (-(rate/4) *
    (cheapSlope shape rate*(R : ℝ)-coordinateAllowance shape rate*(d : ℝ)))

noncomputable def meanLocalizationAllowance (shape rate : ℝ) (d R : ℕ) : ℝ :=
  sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2) *
    sqrt (localizationErrorBound shape rate d R)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Unrestricted centered Gamma passage-time concentration with an explicit
localization allowance and constants depending only on the shape and rate. -/
theorem GammaEnvironment.passageTime_centered_exponential
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (t : ℝ) :
    P.real {ω | t*sqrt R + meanLocalizationAllowance shape rate (latticeDistance p q) R ≤
      |PlanarFPP.passageTime (fun e => τ e ω) p q -
        ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) +
        localizationErrorBound shape rate (latticeDistance p q) R := by
  obtain ⟨hzero, hgap⟩ := h.localPassageTime_mean_gap_le hs hr p q R hR
  have habs : |(∫ η, FiniteLocal.passageTime (fun e => τ e η) p q R ∂P) -
      ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P| ≤
      meanLocalizationAllowance shape rate (latticeDistance p q) R := by
    rw [abs_of_nonneg hzero]
    exact hgap
  exact h.passageTime_centered_exponential_of_mean_gap hs hr p q R hR _ habs t

/-- Equivalent arbitrary absolute-deviation threshold. sqrt R is positive
because d<R, even at p=q. The explicit error need not be small for small R. -/
theorem GammaEnvironment.passageTime_centered_exponential_at
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (u : ℝ) :
    P.real {ω | u ≤ |PlanarFPP.passageTime (fun e => τ e ω) p q -
      ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate *
        ((u-meanLocalizationAllowance shape rate (latticeDistance p q) R)/sqrt R)) +
        localizationErrorBound shape rate (latticeDistance p q) R := by
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hsqrt : 0 < sqrt (R : ℝ) := sqrt_pos.mpr (by exact_mod_cast hpos)
  have ht := h.passageTime_centered_exponential hs hr p q R hR
    ((u-meanLocalizationAllowance shape rate (latticeDistance p q) R)/sqrt R)
  have he : (u-meanLocalizationAllowance shape rate (latticeDistance p q) R)/sqrt R *
      sqrt R + meanLocalizationAllowance shape rate (latticeDistance p q) R = u := by
    rw [div_mul_cancel₀ _ hsqrt.ne']
    ring
  rw [he] at ht
  exact ht

end GammaFPP

end OAI
