import OAI.Analysis.CircleDomains.Probability.ClosedSubsetHitFusion
import OAI.Analysis.CircleDomains.Probability.ProbabilityMixtureMap
import OAI.Analysis.CircleDomains.Probability.PublishedProbabilityTopology

namespace OAI

/-! Apply compact-dust fusion to a Borel, mixture-closed family of code laws.
The compatible Polish refinement is constructed from the published
probability-space topology inputs and Mathlib's refinement theorem. -/

open Set Function MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace Ω]

theorem exists_law_in_borel_family_with_hit_bound
    (hstandard : StandardBorelProbabilityLaws Ω)
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (A : Set (ProbabilityMeasure Ω)) (hA : MeasurableSet A)
    (f : Ω → C(PathTime, X)) (hf : Measurable f)
    (hmix : ∀ (P : ProbabilityMeasure (ℕ → ℕ))
      (law : (ℕ → ℕ) → ProbabilityMeasure Ω) (hlaw : Measurable law),
      (∀ z, law z ∈ A) → probabilityMixture P law hlaw ∈ A)
    (B : Set X) (hB : IsClosed B) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ μ ∈ A, PassesHitTests C (μ.map f) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ ∈ A,
      (∀ F : Finset B, ∑ x ∈ F, pathHitReal (μ.map f) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ B ∧ 0 < pathHitProbability (μ.map f) x}.Countable := by
  let : StandardBorelSpace (ProbabilityMeasure Ω) := hstandard
  let : PolishSpace (ProbabilityMeasure C(PathTime, X)) := hpath.1
  let : BorelSpace (ProbabilityMeasure C(PathTime, X)) := hpath.2
  let : StandardBorelSpace A := hA.standardBorel
  let := upgradeStandardBorel A
  let law : A → ProbabilityMeasure C(PathTime, X) := fun μ => μ.val.map f
  have hm : Measurable law := (measurable_probability_pushforward f hf).comp
    measurable_subtype_coe
  obtain ⟨t, hle, hc, ht⟩ := hm.exists_continuous
  have hbe : @BorelSpace A t inferInstance := by
    constructor
    rw [eq_borel_upgradeStandardBorel A, borel_eq_borel_of_le ht _ hle]
    infer_instance
  let : TopologicalSpace A := t
  let : PolishSpace A := ht
  let : BorelSpace A := hbe
  let := upgradeIsCompletelyMetrizable A
  have htest' : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ μ : A, PassesHitTests C (law μ) D ν := by
    intro D hD hDB ν hν hn hs
    obtain ⟨μ, hμ, hh⟩ := htest D hD hDB ν hν hn hs
    exact ⟨⟨μ, hμ⟩, hh⟩
  obtain ⟨P, e, hF, hcount⟩ :=
    exists_hit_norm_mixture_on_closed_subset B hB law hc hC htest' hε
  let codeLaw : (ℕ → ℕ) → ProbabilityMeasure Ω := fun z => (e z).val
  have hcode : Measurable codeLaw := measurable_subtype_coe.comp e.continuous.measurable
  let μ : ProbabilityMeasure Ω := probabilityMixture P codeLaw hcode
  have hmap : μ.map f = probabilityMixture P (law ∘ e)
      (measurable_of_continuous_probability (hc.comp e.continuous)) := by
    exact probabilityMixture_map P codeLaw hcode f hf
  refine ⟨μ, hmix P codeLaw hcode (fun z => (e z).property), ?_, ?_⟩
  · simpa only [hmap] using hF
  · simpa only [hmap] using hcount

end CircleDomainRigidity

end

end OAI
