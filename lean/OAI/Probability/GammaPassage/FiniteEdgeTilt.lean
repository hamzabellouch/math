import OAI.Probability.GammaPassage.TiltComparison
import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.GridIndependence

namespace OAI

namespace GammaFPP.Tilt
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

open GammaFPP.Grid

noncomputable def scaleFiniteEdges (S : Finset Edge) (α : ℝ) (w : Edge → ℝ) : Edge → ℝ :=
  fun e => if e ∈ S then α*w e else w e

theorem scaleFiniteEdges_event_iff (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ))
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    scaleFiniteEdges S α w ∈ A ↔ (fun e => α*w e) ∈ A := by
  apply hA
  intro e he
  simp [scaleFiniteEdges,he]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- Exact reduction of a supported configuration event to its finite law. -/
theorem finite_support_event_probability (h : GammaEnvironment shape rate P τ)
    (S : Finset Edge) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | (fun e => τ e ω) ∈ A}=
      (Measure.pi (fun _ : S => gammaMeasure shape rate)) ((extendEdgeWeights S) ⁻¹' A) := by
  rw [← h.finiteJointLaw S,Measure.map_apply (Measurable.of_eval (fun e : S => h.measurable e))
    (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  exact (hS.restriction_iff (fun e => τ e ω)).symm

theorem finite_support_scaled_event_probability (h : GammaEnvironment shape rate P τ)
    (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
      ((Measure.pi (fun _ : S => gammaMeasure shape rate)).map (fun x e => α*x e))
        ((extendEdgeWeights S) ⁻¹' A) := by
  have hm : Measurable (fun ω (e : S) => α*τ e ω) :=
    Measurable.of_eval (fun e => measurable_const.mul (h.measurable e))
  rw [← h.finiteJointLaw S,Measure.map_map (by fun_prop)
    (Measurable.of_eval (fun e : S => h.measurable e))]
  change P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
    (P.map (fun ω (e : S) => α*τ e ω)) ((extendEdgeWeights S) ⁻¹' A)
  rw [Measure.map_apply hm (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  rw [mem_ofPred_eq,scaleFiniteEdges_event_iff S α A hS]
  exact (hS.restriction_iff (fun e => α*τ e ω)).symm

/-- Exact Gamma cost: the shape factor is retained for every positive shape. -/
theorem finite_edge_tilt_probability_sq_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (δ : ℝ) (hlo : -1 < δ) (hhi : δ < 1)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      (1-δ^2)^(-shape * (S.card : ℝ)) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  have hh := finite_gamma_scaled_probability_sq_bound hs hr hlo hhi
    ((extendEdgeWeights S) ⁻¹' A) (hA.preimage (measurable_extendEdgeWeights S))
  unfold Measure.real at *
  rw [finite_support_scaled_event_probability h S (1-δ) A hA hS,
    finite_support_event_probability h S A hA hS]
  simpa only [finiteGammaMeasure, Fintype.card_coe] using hh

end GammaFPP.Tilt

end OAI
