import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedGoodSetSelection
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # Good sampled profiles on a fixed compact set -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Pull the shrinking neighborhoods back to the actual independent
sample space. Every retained sample approximates the prescribed supported
profile, and their probability still has a subexponential lower bound. -/
theorem exists_good_sampled_observations
    {X A E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A] [NormedAddCommGroup E]
    (samples : ℝ → ProbabilityMeasure A) (profile : ℝ → A → X)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (samples r) (profile r)) atTop (𝓝 ν))
    {f : X} (hf : f ∈ (ν : Measure X).support) (observe : C(X, E)) :
    ∃ (B : ℝ → Set A) (ε : ℝ → ℝ),
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, 0 < ε r) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBound (fun r => ((samples r : Measure A) (B r)).toReal) ∧
      ∀ r a, a ∈ B r → ‖observe (profile r a) - observe f‖ < ε r := by
  let U : ℕ → Set X := fun j => observe ⁻¹' Metric.ball (observe f) (1 / ((j : ℝ) + 1))
  have hU (j : ℕ) : IsOpen (U j) := Metric.isOpen_ball.preimage observe.continuous
  have hfU (j : ℕ) : f ∈ U j := by
    change dist (observe f) (observe f) < 1 / ((j : ℝ) + 1)
    simp only [dist_self]
    positivity
  obtain ⟨k, hk, hmass⟩ := exists_supported_good_sets_subexponential hν hf U hU hfU
  let B := fun r => profile r ⁻¹' U (k r)
  let ε := fun r => 1 / ((k r : ℝ) + 1)
  refine ⟨B, ε, fun r => (hp r) (hU (k r)).measurableSet, ?_, ?_, ?_, ?_⟩
  · intro r
    dsimp [ε]
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  · have heq (r : ℝ) :
        (ProbabilityMeasure.map (samples r) (profile r) : Measure X) (U (k r)) =
          (samples r : Measure A) (B r) := by
      change Measure.map (profile r) (samples r : Measure A) (U (k r)) = _
      exact Measure.map_apply (hp r) (hU (k r)).measurableSet
    simpa only [heq] using hmass
  · intro r a ha
    change dist (observe (profile r a)) (observe f) < ε r at ha
    simpa only [dist_eq_norm] using ha

/-- The observable needed in the segment argument is restriction of a
continuous profile to one fixed compact set. Its norm is the uniform norm. -/
theorem exists_good_sampled_profiles
    {V W A : Type*} [TopologicalSpace V] [NormedAddCommGroup W]
    [MeasurableSpace A] (S : Set C(V, W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (samples : ℝ → ProbabilityMeasure A) (profile : ℝ → A → S)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (samples r) (profile r)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (B : ℝ → Set A) (ε : ℝ → ℝ),
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, 0 < ε r) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBound (fun r => ((samples r : Measure A) (B r)).toReal) ∧
      ∀ r a, a ∈ B r → ∀ z ∈ K, ‖(profile r a).val z - f.val z‖ < ε r := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : C(K, V) := ⟨Subtype.val, continuous_subtype_val⟩
  let observe : C(S, C(K, W)) := ⟨fun g => g.val.comp incl,
    (ContinuousMap.continuous_precomp incl).comp continuous_subtype_val⟩
  obtain ⟨B, ε, hB, hε, hlim, hmass, hclose⟩ :=
    exists_good_sampled_observations samples profile hp ν hν hf observe
  refine ⟨B, ε, hB, hε, hlim, hmass, ?_⟩
  intro r a ha z hz
  have h := (observe (profile r a) - observe f).norm_coe_le_norm ⟨z, hz⟩
  exact h.trans_lt (hclose r a ha)

end PolycyclicRecognition

end

end OAI
