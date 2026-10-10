import Mathlib.MeasureTheory.Measure.Prokhorov
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMomentCompactness

namespace OAI

namespace Balanced.ProfileWeakCompactness
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal

theorem exists_finiteMeasure_subsequence
    {E : Type*} [TopologicalSpace E] [T2Space E] [PseudoMetrizableSpace E]
    [SeparableSpace E] [CompactSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (C : ℝ≥0) (μ : ℕ → FiniteMeasure E) (hμ : ∀ n, (μ n).mass ≤ C) :
    ∃ ν : FiniteMeasure E, ν.mass ≤ C ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  let x : ℕ → ℝ≥0 × ProbabilityMeasure E := fun n => ((μ n).mass, (μ n).normalize)
  have hx : ∀ n, x n ∈ (Set.Icc 0 C) ×ˢ (Set.univ : Set (ProbabilityMeasure E)) := by
    intro n
    exact ⟨⟨bot_le, hμ n⟩, Set.mem_univ _⟩
  obtain ⟨a, ha, φ, hφ, ht⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure E)))).tendsto_subseq hx
  let f : ℝ≥0 × ProbabilityMeasure E → FiniteMeasure E :=
    fun a => a.1 • a.2.toFiniteMeasure
  have hf : Continuous f := by
    exact continuous_fst.smul (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd)
  have hlim : Tendsto (μ ∘ φ) atTop (𝓝 (f a)) := by
    have he : μ ∘ φ = f ∘ (x ∘ φ) := by
      funext n
      exact (μ (φ n)).self_eq_mass_smul_normalize
    rw [he]
    exact (hf.tendsto a).comp ht
  refine ⟨f a, ?_, φ, hφ, hlim⟩
  have hm : Tendsto (fun n => (μ (φ n)).mass) atTop (𝓝 (f a).mass) := hlim.mass
  exact le_of_tendsto hm (Filter.Eventually.of_forall fun n => hμ (φ n))

theorem exists_simultaneous_subsequence
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X]
    [TopologicalSpace E] [T2Space E] [PseudoMetrizableSpace E]
    [SeparableSpace E] [CompactSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (x : ℕ → X) (C D : ℝ≥0) (μ ν : ℕ → FiniteMeasure E)
    (hμ : ∀ n, (μ n).mass ≤ C) (hν : ∀ n, (ν n).mass ≤ D) :
    ∃ a : X, ∃ μ₀ ν₀ : FiniteMeasure E,
      μ₀.mass ≤ C ∧ ν₀.mass ≤ D ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) ∧
      Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  obtain ⟨a, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq x
  obtain ⟨μ₀, hμ₀, ψ, hψ, hμt⟩ :=
    exists_finiteMeasure_subsequence C (μ ∘ φ) (fun n => hμ (φ n))
  obtain ⟨ν₀, hν₀, χ, hχ, hνt⟩ :=
    exists_finiteMeasure_subsequence D (ν ∘ φ ∘ ψ) (fun n => hν (φ (ψ n)))
  refine ⟨a, μ₀, ν₀, hμ₀, hν₀, φ ∘ ψ ∘ χ, hφ.comp (hψ.comp hχ), ?_, ?_, ?_⟩
  · exact (ht.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop
  · exact hμt.comp hχ.tendsto_atTop
  · exact hνt

theorem nonempty_profiles (M : ℝ) (hM : 0 ≤ M) :
    Nonempty (ProfileMomentCompactness.profiles M) := by
  classical
  let p : ProfileMomentCompactness.Index → ℝ := fun i => if i = (0, 0) then 1 else 0
  refine ⟨⟨p, ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [p]
    split_ifs <;> norm_num
  · exact hasSum_ite_eq (0, 0) 1
  · intro s
    have hz : ∀ i, ProfileMomentCompactness.weight i * p i = 0 := by
      intro i
      by_cases hi : i = (0, 0)
      · simp [hi, ProfileMomentCompactness.weight]
      · simp [p, hi]
    simpa only [hz, Finset.sum_const_zero] using hM

theorem exists_profile_measure_subsequence (M : ℝ) (hM : 0 ≤ M)
    (C : ℝ≥0) (μ : ℕ → FiniteMeasure (ProfileMomentCompactness.profiles M))
    (hμ : ∀ n, (μ n).mass ≤ C) :
    ∃ ν : FiniteMeasure (ProfileMomentCompactness.profiles M), ν.mass ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  let : CompactSpace (ProfileMomentCompactness.profiles M) :=
    isCompact_iff_compactSpace.mp (ProfileMomentCompactness.isCompact_profiles M hM)
  let : Nonempty (ProfileMomentCompactness.profiles M) := nonempty_profiles M hM
  exact exists_finiteMeasure_subsequence C μ hμ

theorem mass_eq_of_weak_limit
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E} {c : ℝ≥0}
    (hμ : Tendsto μ atTop (𝓝 ν))
    (hc : Tendsto (fun n => (μ n).mass) atTop (𝓝 c)) : ν.mass = c :=
  tendsto_nhds_unique hμ.mass hc

theorem tendsto_integral_coordinate (M : ℝ) (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure (ProfileMomentCompactness.profiles M)}
    {ν : FiniteMeasure (ProfileMomentCompactness.profiles M)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (i : ℕ × ℕ) :
    Tendsto (fun n => ∫ P, P.val i ∂(μ n).toMeasure) atTop
      (𝓝 (∫ P, P.val i ∂ν.toMeasure)) := by
  let : CompactSpace (ProfileMomentCompactness.profiles M) :=
    isCompact_iff_compactSpace.mp (ProfileMomentCompactness.isCompact_profiles M hM)
  let f : C(ProfileMomentCompactness.profiles M, ℝ) :=
    ⟨fun P => P.val i, (continuous_apply i).comp continuous_subtype_val⟩
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
    (BoundedContinuousFunction.mkOfCompact f)

theorem exists_full_profile_subsequence (M : ℝ) (hM : 0 ≤ M)
    (c : ℕ → ℝ) (hc : ∀ n, c n ∈ Set.Icc (0 : ℝ) 1)
    (p : ℕ → ProfileMomentCompactness.profiles M)
    (C D : ℝ≥0)
    (μ ν : ℕ → FiniteMeasure (ProfileMomentCompactness.profiles M))
    (hμ : ∀ n, (μ n).mass ≤ C) (hν : ∀ n, (ν n).mass ≤ D) :
    ∃ c₀ ∈ Set.Icc (0 : ℝ) 1, ∃ P : ProfileMomentCompactness.profiles M,
      ∃ μ₀ ν₀ : FiniteMeasure (ProfileMomentCompactness.profiles M),
      μ₀.mass ≤ C ∧ ν₀.mass ≤ D ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (c ∘ φ) atTop (𝓝 c₀) ∧ Tendsto (p ∘ φ) atTop (𝓝 P) ∧
      Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  let : CompactSpace (ProfileMomentCompactness.profiles M) :=
    isCompact_iff_compactSpace.mp (ProfileMomentCompactness.isCompact_profiles M hM)
  let : Nonempty (ProfileMomentCompactness.profiles M) := nonempty_profiles M hM
  let x : ℕ → Set.Icc (0 : ℝ) 1 × ProfileMomentCompactness.profiles M :=
    fun n => (⟨c n, hc n⟩, p n)
  obtain ⟨a, μ₀, ν₀, hμ₀, hν₀, φ, hφ, hx, hμt, hνt⟩ :=
    exists_simultaneous_subsequence x C D μ ν hμ hν
  exact ⟨a.1.val, a.1.property, a.2, μ₀, ν₀, hμ₀, hν₀, φ, hφ,
    (continuous_subtype_val.tendsto a.1).comp ((continuous_fst.tendsto a).comp hx),
    (continuous_snd.tendsto a).comp hx, hμt, hνt⟩

end Balanced.ProfileWeakCompactness

end OAI
