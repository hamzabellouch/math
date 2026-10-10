import OAI.Probability.FirstPassage.FiniteEdgeEvents
import OAI.Probability.FirstPassage.TiltComparison

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def scaleFiniteEdges (S : Finset Edge) (α : ℝ) (w : Edge → ℝ) : Edge → ℝ :=
  fun e => if e ∈ S then α*w e else w e

theorem scaleFiniteEdges_event_iff (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ))
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    scaleFiniteEdges S α w ∈ A ↔ (fun e => α*w e) ∈ A := by
  apply hA
  intro e he
  simp [scaleFiniteEdges,he]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.finiteJointLaw (h : ExponentialEnvironment P τ) (S : Finset Edge) :
    P.map (fun ω (e : S) => τ e ω)=Measure.pi (fun _ : S => expMeasure 1) := by
  have hi := h.independent.precomp (Subtype.val_injective : Function.Injective (fun e : S => (e : Edge)))
  rw [iIndepFun.map_fun_eq_pi_map (fun e : S => (h.measurable e).aemeasurable) hi]
  simp only [h.marginal]

theorem finite_support_event_probability (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | (fun e => τ e ω) ∈ A}=
      (Measure.pi (fun _ : S => expMeasure 1)) ((extendEdgeWeights S) ⁻¹' A) := by
  rw [← h.finiteJointLaw S,Measure.map_apply (Measurable.of_eval (fun e : S => h.measurable e))
    (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  exact (hS.restriction_iff (fun e => τ e ω)).symm

theorem finite_support_scaled_event_probability (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
      ((Measure.pi (fun _ : S => expMeasure 1)).map (fun x e => α*x e))
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

theorem finite_edge_tilt_probability_sq_bound (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      (1/(1-δ^2))^S.card * P.real {ω | (fun e => τ e ω) ∈ A} := by
  have hh := finite_scaled_expMeasure_probability_sq_bound δ hδ hδ'
    ((extendEdgeWeights S) ⁻¹' A) (hA.preimage (measurable_extendEdgeWeights S))
  unfold Measure.real at *
  rw [finite_support_scaled_event_probability h S (1-δ) A hA hS,
    finite_support_event_probability h S A hA hS]
  simpa only [Fintype.card_coe] using hh

theorem finite_edge_tilt_probability_sq_exp_bound (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      Real.exp (2*S.card*δ^2) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  exact (finite_edge_tilt_probability_sq_bound h S δ hδ hδ' A hA hS).trans
    (mul_le_mul_of_nonneg_right (likelihood_power_bound δ hδ hδ' S.card) measureReal_nonneg)

end PlanarFPP

end OAI
