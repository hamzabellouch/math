import OAI.Combinatorics.BalancedRyser.Probability.IndependentDoobGrouping
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialGrouping
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialIncrement
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialPrefix
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialReassembly

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ j, MeasurableSpace (A j)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ∀ j, Ω → A j}

theorem doob_increment_bound_of_grouping
    (hξ : ∀ j, Measurable (ξ j))
    (F : (∀ j, A j) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (trialVector ξ ω)) μ)
    (c : Fin T → ℝ) (hosc : CoordinateOscillation F c) (i : Fin T)
    (hindCurrent : IndepFun (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) (ξ i) μ)
    (hindFuture : IndepFun
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω))
      (fun ω (j : {j : Fin T // i.val < j.val}) => ξ j ω) μ)
    (hPast : (inferInstance : MeasurableSpace (∀ j : {j : Fin T // j.val < i.val}, A j)).comap
      (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) = prefixFiltration ξ hξ i.val)
    (hNext : (inferInstance : MeasurableSpace
      ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i)).comap
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω)) =
        prefixFiltration ξ hξ (i.val + 1)) :
    ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ (i.val + 1) ω -
        doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ i.val ω| ≤ c i := by
  classical
  let P := fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω
  let Q := fun ω (j : {j : Fin T // i.val < j.val}) => ξ j ω
  have hP : Measurable P := Measurable.of_eval (fun index => hξ index)
  have hQ : Measurable Q := Measurable.of_eval (fun index => hξ index)
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  let x₀ := trialVector ξ ω₀
  let f := fun p : ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i) ×
      (∀ j : {j : Fin T // i.val < j.val}, A j) => F (reassembleAt i p.1.1 p.1.2 p.2)
  have hf : StronglyMeasurable f := (hF.comp (measurable_reassembleAt i)).stronglyMeasurable
  have hreconstruct (ω : Ω) : reassembleAt i (P ω) (ξ i ω) (Q ω) = trialVector ξ ω :=
    reassembleAt_restrict i (trialVector ξ ω)
  have hfi : Integrable (fun ω => f ((P ω, ξ i ω), Q ω)) μ := by
    simpa only [f, hreconstruct] using hFi
  have hfslice (x : ∀ j : {j : Fin T // j.val < i.val}, A j) (z : A i) :
      Integrable (fun v => f ((x, z), v)) (μ.map Q) := by
    exact hosc.integrable_comp hF x₀
      ((measurable_reassembleAt i).comp (measurable_const.prodMk measurable_id))
  have hHslice (x : ∀ j : {j : Fin T // j.val < i.val}, A j) :
      Integrable (fun z => ∫ v, f ((x, z), v) ∂(μ.map Q)) (μ.map (ξ i)) := by
    have hpair : Integrable (fun p : A i × (∀ j : {j : Fin T // i.val < j.val}, A j) =>
        f ((x, p.1), p.2)) ((μ.map (ξ i)).prod (μ.map Q)) :=
      hosc.integrable_comp hF x₀ ((measurable_reassembleAt i).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    exact hpair.integral_prod_left
  have hosc' (x : ∀ j : {j : Fin T // j.val < i.val}, A j) (z z' : A i) :
      ∀ᵐ v ∂(μ.map Q), |f ((x, z), v) - f ((x, z'), v)| ≤ c i := by
    filter_upwards with v
    exact hosc i _ _ (fun j hji => reassembleAt_eq_of_ne i x z z' v j hji)
  have hbound := independent_three_block_increment_bound hP (hξ i) hQ
    hindCurrent hindFuture hf hfi hfslice hHslice hosc'
  simpa only [f, hreconstruct, P, Q, hPast, hNext, doobProcess] using hbound

theorem doob_increment_bound
    (hξ : ∀ j, Measurable (ξ j)) (hind : iIndepFun ξ μ)
    (F : (∀ j, A j) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (trialVector ξ ω)) μ)
    (c : Fin T → ℝ) (hosc : CoordinateOscillation F c) (i : Fin T) :
    ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ (i.val + 1) ω -
        doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ i.val ω| ≤ c i :=
  doob_increment_bound_of_grouping hξ F hF hFi c hosc i
    (independent_past_current hξ hind i)
    (independent_past_current_future hξ hind i)
    (comap_past_eq_prefixFiltration hξ i)
    (comap_past_current_eq_prefixFiltration hξ i)

end Balanced.IndependentTrials

end OAI
