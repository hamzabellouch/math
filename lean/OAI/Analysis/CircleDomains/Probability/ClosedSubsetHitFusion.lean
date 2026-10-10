import OAI.Analysis.CircleDomains.Probability.MarkedHitFusion

namespace OAI

/-! The fusion theorem applied to a closed dust subset. Its tests are ordinary
ambient measures supported on the dust, exactly as in the modulus extraction. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MetricSpace Z] [SecondCountableTopology Z] [CompleteSpace Z]

theorem exists_hit_norm_mixture_on_closed_subset
    (B : Set X) (hB : IsClosed B)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Continuous law)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ z, PassesHitTests C (law z) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      let μ := probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))
      (∀ F : Finset B, ∑ x ∈ F, pathHitReal μ x.val ^ 2 ≤ (C + ε) ^ 2) ∧
        {x : X | x ∈ B ∧ 0 < pathHitProbability μ x}.Countable := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let ι : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have htest' : ∀ D : Set B, D.Countable → ∀ ν : Measure B,
      IsFiniteMeasure ν → NullSingletonClass ν →
        ∃ z, MarkedHit.PassesHitTests ι C (law z) D ν := by
    intro D hD ν hν hnull
    let : IsFiniteMeasure ν := hν
    let : NullSingletonClass ν := hnull
    let ρ : Measure X := ν.map (Subtype.val : B → X)
    have hρ : IsFiniteMeasure ρ := inferInstance
    have hρnull : NullSingletonClass ρ := by
      constructor
      intro x
      rw [show ρ = ν.map (Subtype.val : B → X) from rfl,
        Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton x)]
      by_cases hx : x ∈ B
      · have he : (Subtype.val : B → X) ⁻¹' {x} = {⟨x, hx⟩} := by
          ext y
          simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
        rw [he]
        exact measure_singleton _
      · have he : (Subtype.val : B → X) ⁻¹' {x} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx ((mem_singleton_iff.mp hy) ▸ y.property)
        rw [he, measure_empty]
    have hρB : ρ Bᶜ = 0 := by
      rw [show ρ = ν.map (Subtype.val : B → X) from rfl,
        Measure.map_apply continuous_subtype_val.measurable hB.measurableSet.compl]
      simp
    obtain ⟨z, hz⟩ := htest (Subtype.val '' D) (hD.image _) (by
      rintro x ⟨y, _, rfl⟩
      exact y.property) ρ hρ hρnull hρB
    refine ⟨z, ?_, ?_⟩
    · intro F hF
      have hb := hz.1 (F.image (Subtype.val : B → X)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact mem_image_of_mem _ (hF hy))
      simpa only [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h),
        MarkedHit.pathHitReal, MarkedHit.pathHitProbability, pathHitReal, ι,
        ContinuousMap.coe_mk] using hb
    · change ∫⁻ x, pathHitProbability (law z) (x : X) ∂ν = 0
      rw [← lintegral_map (measurable_pathHitProbability_point (law z))
        continuous_subtype_val.measurable]
      exact hz.2
  obtain ⟨P, e, hb⟩ := MarkedHit.exists_hit_norm_mixture_of_countable_tests ι hlaw hC htest' hε
  refine ⟨P, e, hb, ?_⟩
  have hcount := hb.countable_positive_support
  have heq : Subtype.val '' {x : B | 0 < MarkedHit.pathHitProbability ι
      (probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))) x} =
      {x : X | x ∈ B ∧ 0 < pathHitProbability
        (probabilityMixture P (law ∘ e)
          (measurable_of_continuous_probability (hlaw.comp e.continuous))) x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hh⟩
      exact ⟨⟨x, hx⟩, hh, rfl⟩
  rw [← heq]
  exact hcount.image _

end CircleDomainRigidity

end

end OAI
