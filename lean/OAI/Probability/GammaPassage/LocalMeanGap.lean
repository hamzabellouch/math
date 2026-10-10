import OAI.Probability.GammaPassage.LocalCoordinateDomination
import OAI.Probability.GammaPassage.LocalizationProbability
import OAI.Probability.GammaPassage.PathSecondMoment
import OAI.Probability.GammaPassage.LocalLawTransfer
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

/-- Cauchy–Schwarz bounds an integral restricted to a measurable event. -/
lemma integral_indicator_le_sqrt_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet E)
    (hS : MemLp S 2 P) (hpos : 0 ≤ᵐ[P] S) :
    (∫ ω, E.indicator S ω ∂P) ≤
      Real.sqrt (∫ ω, (S ω)^2 ∂P) * Real.sqrt (P.real E) := by
  have hI : MemLp (E.indicator (fun _ : Ω => (1 : ℝ))) 2 P :=
    (memLp_const (1 : ℝ)).indicator hE
  have hIpos : 0 ≤ᵐ[P] (E.indicator (fun _ : Ω => (1 : ℝ))) := by
    filter_upwards [] with ω
    by_cases he : ω ∈ E <;> simp [he]
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hpos hIpos (by simpa using hS) (by simpa using hI)
  have hi : (∫ ω, (E.indicator (fun _ : Ω => (1 : ℝ)) ω)^(2 : ℝ) ∂P) = P.real E := by
    have heq : (fun ω => (E.indicator (fun _ : Ω => (1 : ℝ)) ω)^(2 : ℝ)) =
        E.indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      by_cases he : ω ∈ E <;> simp [he]
    rw [heq, integral_indicator_const (1 : ℝ) hE]
    simp
  have hprod : (fun ω => S ω * E.indicator (fun _ : Ω => (1 : ℝ)) ω) =
      E.indicator S := by
    funext ω
    by_cases he : ω ∈ E <;> simp [he]
  rw [hi, hprod] at hc
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The gap between local and unrestricted passage times is nonnegative and
bounded by the coordinate-path cost on the event where they differ. -/
theorem GammaEnvironment.ae_localPassageTime_gap_indicator
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∀ᵐ ω ∂P,
      0 ≤ FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ∧
      FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ≤
      {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q}.indicator
          (fun ω => pathCost (fun e => τ e ω) p (coordinatePath p q)) ω := by
  filter_upwards [h.ae_positive_edges] with ω hpos
  have hw : ∀ e, 0 ≤ τ e ω := fun e => (hpos e).le
  have hlo := FiniteLocal.unrestricted_passageTime_le (fun e => τ e ω) hw p q R hR
  have hup := FiniteLocal.passageTime_le_coordinatePath (fun e => τ e ω) hw p q R hR
  have ht := PlanarFPP.passageTime_nonneg (fun e => τ e ω) hw p q
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  by_cases he : FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q
  · have hmem : ω ∈ {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q} := he
    rw [Set.indicator_of_mem hmem]
    linarith
  · have heq := not_ne_iff.mp he
    simp [heq]

/-- The difference of the local and unrestricted mean passage times is controlled
by the coordinate-path second moment and the localization probability. -/
theorem GammaEnvironment.localPassageTime_mean_gap_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    0 ≤ (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      (∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P) ∧
    (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      (∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P) ≤
      Real.sqrt (pathSecondMomentConstant shape rate * (latticeDistance p q : ℝ)^2) *
      Real.sqrt ((1 / 2 : ℝ)^R + 2 * Real.exp (-(rate / 4) *
        (cheapSlope shape rate * (R : ℝ) -
          coordinateAllowance shape rate * (latticeDistance p q : ℝ)))) := by
  let := h.probability
  let E : Set Ω := {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
    PlanarFPP.passageTime (fun e => τ e ω) p q}
  let S : Ω → ℝ := fun ω => pathCost (fun e => τ e ω) p (coordinatePath p q)
  have hE : MeasurableSet E := h.measurableSet_localization_error p q R hR
  have hSlp : MemLp S 2 P := h.pathCost_memLp_two hs hr p (coordinatePath p q)
  have hSi : Integrable S P := h.integrable_pathCost hs hr p (coordinatePath p q)
  have hSpos : 0 ≤ᵐ[P] S := by
    filter_upwards [h.ae_positive_edges] with ω hpos
    exact pathCost_nonneg (fun e => (hpos e).le) _ _
  have hLi := h.integrable_localPassageTime hs hr p q R hR
  have hTi := h.integrable_passageTime hs hr p q
  have hgap := h.ae_localPassageTime_gap_indicator p q R hR
  simp only [← integral_sub hLi hTi]
  refine ⟨integral_nonneg_of_ae (hgap.mono fun _ hω => hω.1), ?_⟩
  calc
    _ ≤ ∫ ω, E.indicator S ω ∂P :=
      integral_mono_ae (hLi.sub hTi) (hSi.indicator hE) (hgap.mono fun _ hω => hω.2)
    _ ≤ Real.sqrt (∫ ω, (S ω)^2 ∂P) * Real.sqrt (P.real E) :=
      integral_indicator_le_sqrt_second_moment hE hSlp hSpos
    _ ≤ _ := by
      apply mul_le_mul
      · apply Real.sqrt_le_sqrt
        simpa only [coordinatePath_length_eq_distance] using
          h.coordinatePath_second_moment_le hs hr p q
      · exact Real.sqrt_le_sqrt (h.localization_error_probability_real hs hr p q R hR)
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _
end GammaFPP

end OAI
