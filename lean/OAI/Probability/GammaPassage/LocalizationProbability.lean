import OAI.Probability.GammaPassage.LocalGlobalEquality
import OAI.Probability.GammaPassage.LocalRegularity
import OAI.Probability.GammaPassage.CheapPathDecay
import OAI.Probability.GammaPassage.CoordinateTails
import OAI.Probability.GammaPassage.EnvironmentScaling

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.measurableSet_localization_error
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    MeasurableSet {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} := by
  have hl : Measurable (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) :=
    (FiniteLocal.measurable_passageTime p q R hR).comp
      (Measurable.of_eval h.measurable)
  exact (measurableSet_eq_fun hl (h.measurable_passageTime p q)).compl

theorem GammaEnvironment.localization_error_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    P.real {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} ≤
      (1 / 2 : ℝ)^R + 2 * Real.exp (-(rate / 4) *
        (cheapSlope shape rate * (R : ℝ) -
          coordinateAllowance shape rate * (latticeDistance p q : ℝ))) := by
  let := h.probability
  let B := cheapSlope shape rate * (R : ℝ)
  let A : Set Ω := {ω | ∃ ds : List Step, ds.length = R ∧
    ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ B}
  let C : Set Ω := {ω | B ≤ pathCost (fun e => τ e ω) p (coordinatePath p q)}
  have hsub : {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} ≤ᵐ[P] (A ∪ C : Set Ω) := by
    filter_upwards [h.ae_positive_edges] with ω hpos herror
    by_cases hA : ω ∈ A
    · exact Or.inl hA
    · by_cases hC : ω ∈ C
      · exact Or.inr hC
      · exfalso
        have hcoord : pathCost (fun e => τ e ω) p (coordinatePath p q) < B :=
          lt_of_not_ge hC
        apply herror
        exact FiniteLocal.passageTime_eq_unrestricted_of_no_cheap_trail
          (fun e => τ e ω) (fun e => (hpos e).le) p q R B hR
          ⟨coordinatePath p q, coordinatePath_endpoint p q, hcoord⟩ hA
  have hA : P.real A ≤ (1 / 2 : ℝ)^R :=
    h.cheap_fixed_length_decay_real hs hr p R
  have hC : P.real C ≤ 2 * Real.exp (-(rate / 4) *
      (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ))) := by
    have hc := h.costly_coordinatePath_probability_real hs hr p q
      (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ))
    have he : coordinateAllowance shape rate * (latticeDistance p q : ℝ) +
        (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ)) = B := by ring
    rw [he] at hc
    exact hc
  calc
    _ ≤ P.real (A ∪ C) :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ P.real A + P.real C := measureReal_union_le A C
    _ ≤ _ := add_le_add hA hC

end GammaFPP

end OAI
