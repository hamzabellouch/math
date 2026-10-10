import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GoodProfileSampling

namespace OAI

/-! # Good sheets selected along a converging sequence of profile laws -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem exists_supported_good_sets_sequence
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j)) (hxU : ∀ j, x ∈ U j) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((μs n : Measure X) (U (k n))).toReal) := by
  exact exists_slow_sequence_subexponential_mass scale hs _ (fun j =>
    eventual_positive_mass_of_supported_weak_limit hμ hx (hU j) (hxU j))

theorem exists_good_sampled_observations_sequence
    {X A E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A] [NormedAddCommGroup E]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → X)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (profile n)) atTop (𝓝 ν))
    {f : X} (hf : f ∈ (ν : Measure X).support) (observe : C(X, E)) :
    ∃ (B : ℕ → Set A) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (B n)) ∧ (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((samples n : Measure A) (B n)).toReal) ∧
      ∀ n a, a ∈ B n → ‖observe (profile n a) - observe f‖ < ε n := by
  let U : ℕ → Set X := fun j => observe ⁻¹' Metric.ball (observe f) (1 / ((j : ℝ) + 1))
  have hU (j : ℕ) : IsOpen (U j) := Metric.isOpen_ball.preimage observe.continuous
  have hfU (j : ℕ) : f ∈ U j := by
    change dist (observe f) (observe f) < 1 / ((j : ℝ) + 1)
    simp only [dist_self]
    positivity
  obtain ⟨k, hk, hmass⟩ := exists_supported_good_sets_sequence scale hs hν hf U hU hfU
  let B := fun n => profile n ⁻¹' U (k n)
  let ε := fun n => 1 / ((k n : ℝ) + 1)
  refine ⟨B, ε, fun n => (hp n) (hU (k n)).measurableSet, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [ε]
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  · have heq (n : ℕ) :
        (ProbabilityMeasure.map (samples n) (profile n) : Measure X) (U (k n)) =
          (samples n : Measure A) (B n) := by
      exact Measure.map_apply (hp n) (hU (k n)).measurableSet
    simpa only [heq] using hmass
  · intro n a ha
    change dist (observe (profile n a)) (observe f) < ε n at ha
    simpa only [dist_eq_norm] using ha

theorem exists_good_sampled_profiles_sequence
    {V W A : Type*} [TopologicalSpace V] [NormedAddCommGroup W]
    [MeasurableSpace A] (S : Set C(V, W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (profile n)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (B : ℕ → Set A) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (B n)) ∧ (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((samples n : Measure A) (B n)).toReal) ∧
      ∀ n a, a ∈ B n → ∀ z ∈ K, ‖(profile n a).val z - f.val z‖ < ε n := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : C(K, V) := ⟨Subtype.val, continuous_subtype_val⟩
  let observe : C(S, C(K, W)) := ⟨fun g => g.val.comp incl,
    (ContinuousMap.continuous_precomp incl).comp continuous_subtype_val⟩
  obtain ⟨B, ε, hB, hε, hlim, hmass, hclose⟩ :=
    exists_good_sampled_observations_sequence scale hs samples profile hp ν hν hf observe
  refine ⟨B, ε, hB, hε, hlim, hmass, ?_⟩
  intro n a ha z hz
  have h := (observe (profile n a) - observe f).norm_coe_le_norm ⟨z, hz⟩
  exact h.trans_lt (hclose n a ha)

end PolycyclicRecognition

end

end OAI
