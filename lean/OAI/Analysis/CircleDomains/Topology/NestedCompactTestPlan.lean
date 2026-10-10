import OAI.Analysis.CircleDomains.Probability.CompactMeasureSeparation
import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureBorel
import OAI.Analysis.CircleDomains.Probability.ClosedProbabilitySupport

namespace OAI

/-! A common continuous-test bound on decreasing compact measure families
passes to a plan supported on their intersection. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma exists_nested_compact_test_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (T : ℕ → Set (FiniteMeasure Z)) (hT : ∀ n, IsCompact (T n))
    (hne : ∀ n, (T n).Nonempty) (hanti : Antitone T)
    (hz : (0 : FiniteMeasure Z) ∉ T 0) {c : ℝ} (hc : 0 < c)
    (hm : ∀ n, ENNReal.ofReal (c^2) < measureFamilyModulus (T n) Z σ (fun v => v.val)) :
    ∃ P : ProbabilityMeasure (T 0),
      (∀ᵐ v ∂(P : Measure (T 0)), v.val ∈ ⋂ n, T n) ∧
      ∀ f : Z →ᵇ ℝ,
        c * (∫ v : T 0, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure (T 0))) ≤
          ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
  classical
  let : CompactSpace (T 0) := isCompact_iff_compactSpace.mp (hT 0)
  let : BorelSpace (T 0) := compact_finiteMeasure_borel (hT 0)
  let : PolishSpace (T 0) := compact_finiteMeasure_polish (hT 0)
  let : PolishSpace (ProbabilityMeasure (T 0)) := compact_probability_polish (T 0)
  have hex (n : ℕ) : ∃ P : ProbabilityMeasure (T n), ∀ f : Z →ᵇ ℝ,
      c * (∫ v : T n, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure (T n))) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    let : CompactSpace (T n) := isCompact_iff_compactSpace.mp (hT n)
    exact exists_compact_measure_test_plan σ (hT n) (hne n)
      (fun h => hz (hanti (Nat.zero_le n) h)) c hc (hm n)
  choose P hP using hex
  let j (n : ℕ) : T n → T 0 := fun v => ⟨v.val,hanti (Nat.zero_le n) v.property⟩
  have hjm (n : ℕ) : Measurable (j n) := by
    exact (show Measurable (fun v : T n => v.val) from measurable_subtype_coe).subtype_mk
  let Q (n : ℕ) : ProbabilityMeasure (T 0) := (P n).map (j n)
  obtain ⟨L,ρ,hρ,hlim⟩ := SeqCompactSpace.tendsto_subseq Q
  refine ⟨L,?_,?_⟩
  · have hs (n : ℕ) : ∀ᵐ v ∂(L : Measure (T 0)), v.val ∈ T n := by
      have hF : IsClosed {v : T 0 | v.val ∈ T n} :=
        (hT n).isClosed.preimage continuous_subtype_val
      apply probability_supported_closed_of_tendsto hlim hF
      filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
      change ∀ᵐ v ∂(P (ρ k) : Measure (T (ρ k))).map (j (ρ k)), v.val ∈ T n
      apply (ae_map_iff (hjm (ρ k)).aemeasurable hF.measurableSet).mpr
      exact Eventually.of_forall (fun v => hanti hk v.property)
    filter_upwards [ae_all_iff.mpr hs] with v hv
    exact mem_iInter.mpr hv
  · intro f
    have ht : Tendsto (fun k => ∫ v : T 0, compactMeasureTestOperator (T 0) f v
        ∂(Q (ρ k) : Measure (T 0))) atTop
        (𝓝 (∫ v : T 0, compactMeasureTestOperator (T 0) f v ∂(L : Measure (T 0)))) :=
      (ProbabilityMeasure.continuous_integral_continuousMap
        (compactMeasureTestOperator (T 0) f)).continuousAt.tendsto.comp hlim
    apply le_of_tendsto (ht.const_mul c)
    apply Eventually.of_forall
    intro k
    change c * (∫ v : T 0, compactMeasureTestOperator (T 0) f v
      ∂(P (ρ k) : Measure (T (ρ k))).map (j (ρ k))) ≤ _
    rw [integral_map (hjm (ρ k)).aemeasurable
      (compactMeasureTestOperator (T 0) f).continuous.measurable.aestronglyMeasurable]
    exact hP (ρ k) f

end CircleDomainRigidity

end

end OAI
