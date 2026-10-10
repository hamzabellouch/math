import OAI.Probability.GammaPassage.LocalLawTransfer
import OAI.Probability.GammaPassage.LocalizationProbability

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Comparing two observables and their centers bounds the probability of a
centered deviation. The estimate holds for arbitrary measures. -/
lemma centered_event_comparison (P : Measure Ω) (X Y : Ω → ℝ)
    (a b s d : ℝ) (hd : |b-a| ≤ d) :
    P {ω | s+d ≤ |X ω-a|} ≤
      P {ω | s ≤ |Y ω-b|} + P {ω | Y ω ≠ X ω} := by
  have hsub : {ω | s+d ≤ |X ω-a|} ⊆
      {ω | s ≤ |Y ω-b|} ∪ {ω | Y ω ≠ X ω} := by
    intro ω hω
    by_cases he : Y ω = X ω
    · left
      change s ≤ |Y ω-b|
      have htri : |X ω-a| ≤ |Y ω-b| + |b-a| := by
        rw [← he]
        simpa only [sub_add_sub_cancel] using abs_add_le (Y ω-b) (b-a)
      change s+d ≤ |X ω-a| at hω
      linarith
    · exact Or.inr he
  exact (measure_mono hsub).trans (measure_union_le _ _)

variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The localization error and a bound on the deterministic mean shift control
unrestricted centered deviations. The case `p = q` is included when `0 < R`. -/
theorem GammaEnvironment.passageTime_centered_exponential_of_mean_gap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (b : ℝ)
    (hb : |(∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      ∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P| ≤ b)
    (t : ℝ) :
    P.real {ω | t*sqrt R+b ≤ |PlanarFPP.passageTime (fun e => τ e ω) p q -
      ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) +
      ((1/2 : ℝ)^R + 2*exp (-(rate/4) *
        (cheapSlope shape rate*(R : ℝ) -
          coordinateAllowance shape rate*(latticeDistance p q : ℝ)))) := by
  let : IsProbabilityMeasure P := h.probability
  let X : Ω → ℝ := fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q
  let Y : Ω → ℝ := fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R
  have hc := centered_event_comparison P X Y (∫ ω, X ω ∂P) (∫ ω, Y ω ∂P)
    (t*sqrt R) b hb
  have hlocal := h.localPassageTime_centered_exponential hs hr p q R hR t
  have hlocalReal : P.real {ω | t*sqrt R ≤ |Y ω-∫ η, Y η ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) := by
    have hfin : (2 : ℝ≥0∞)*ENNReal.ofReal
        (exp (1-FiniteLocal.concentrationKappa shape rate*t)) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    have hh := ENNReal.toReal_mono hfin hlocal
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (exp_pos _).le] using hh
  have hsumfin : P {ω | t*sqrt R ≤ |Y ω-∫ η, Y η ∂P|} +
      P {ω | Y ω ≠ X ω} ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hreal := ENNReal.toReal_mono hsumfin hc
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
  exact hreal.trans (add_le_add hlocalReal
    (h.localization_error_probability_real hs hr p q R hR))

/-- Gamma centered concentration with the difference of the localized and
unrestricted means included in the deviation threshold. -/
theorem GammaEnvironment.passageTime_centered_exponential_shifted
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (t : ℝ) :
    P.real {ω | t*sqrt R +
      |(∫ η, FiniteLocal.passageTime (fun e => τ e η) p q R ∂P) -
        ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P| ≤
      |PlanarFPP.passageTime (fun e => τ e ω) p q -
        ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) +
      ((1/2 : ℝ)^R + 2*exp (-(rate/4) *
        (cheapSlope shape rate*(R : ℝ) -
          coordinateAllowance shape rate*(latticeDistance p q : ℝ)))) :=
  h.passageTime_centered_exponential_of_mean_gap hs hr p q R hR _ le_rfl t

/-- A quantitative separation of the distance and localization scales bounds
the difference between localized and unrestricted means. -/
lemma localization_exponential_scale_separation
    {shape rate d r : ℝ} (hr : 0 < rate)
    (hscale : 2 * coordinateAllowance shape rate * d ≤ cheapSlope shape rate * r) :
    exp (-(rate/4) * (cheapSlope shape rate*r-coordinateAllowance shape rate*d)) ≤
      exp (-(rate*cheapSlope shape rate/8)*r) := by
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hscale hr.le
  nlinarith

end GammaFPP

end OAI
