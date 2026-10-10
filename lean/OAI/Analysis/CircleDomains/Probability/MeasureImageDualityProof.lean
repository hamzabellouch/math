import OAI.Analysis.CircleDomains.Probability.BorelImageCompactModulus
import OAI.Analysis.CircleDomains.Probability.CompactMeasureDuality

namespace OAI

/-! The exact p=2 Borel-image consequence of ADMS Theorem5.1 and Corollary5.2.
All compact approximation, separation, barycenter and null-family steps are
constructed. No duality input is assumed in this proof. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureImageDuality
    (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] :
    MeasureImageDuality A Z := by
  classical
  intro K hK σ hσ c hc hmod
  let : IsFiniteMeasure σ := hσ
  let : MeasurableSingletonClass (FiniteMeasure Z) :=
    ⟨fun v => compact_finiteMeasure_measurableSet isCompact_singleton⟩
  by_cases hz : (0 : FiniteMeasure Z) ∈ range K
  · let η : ProbabilityMeasure (FiniteMeasure Z) := ⟨Measure.dirac 0,inferInstance⟩
    refine ⟨η,fun _ => 0,measurable_const,?_,?_,?_⟩
    · change ∀ᵐ v ∂Measure.dirac (0 : FiniteMeasure Z), v ∈ range K
      filter_upwards [ae_eq_dirac (fun v : FiniteMeasure Z => v)] with v hv
      rw [hv]
      exact hz
    · intro E hE
      change (∫⁻ v : FiniteMeasure Z, (v : Measure Z) E ∂Measure.dirac 0) = σ.withDensity (fun _ => 0) E
      simp
    · simp
  · have hnonzero : ∀ a, K a ≠ 0 := by
      intro a ha
      exact hz ⟨a,ha⟩
    obtain ⟨S,hS,hSK,hSm⟩ := exists_compact_subfamily_of_borel_image σ K hK hnonzero hmod
    have hSn : S.Nonempty := by
      by_contra hn
      let : IsEmpty S := ⟨fun x => hn ⟨x.val,x.property⟩⟩
      rw [measureFamilyModulus_zero_of_isEmpty] at hSm
      exact (not_lt_of_ge bot_le) hSm
    have hSz : (0 : FiniteMeasure Z) ∉ S := fun h => hz (hSK h)
    obtain ⟨η,q,hq,hsupp,hbar,he⟩ := compact_measure_image_duality σ hS hSn hSz c hc hSm
    exact ⟨η,q,hq,hsupp.mono (fun v hv => hSK hv),hbar,he⟩

end CircleDomainRigidity

end

end OAI
