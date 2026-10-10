import OAI.GroupTheory.PolycyclicRecognition.Geometry.GoodProfileFlow
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceProfileSampling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowNeighborhood

namespace OAI

/-! # Selecting good sampled sheets for an entire horizontal segment -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

/-- A supported weak profile limit gives one slowly improving family of
good sheets on a compact neighborhood of the entire actual late segment.
The endpoint scheme can be fixed before this selection. -/
theorem exists_good_profiles_along_segment_sequence
    {V W A : Type*} [MetricSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (samples r) (profile r)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    (Ψ : ℕ → C(V × ℝ, V)) (Ψ₀ : C(V × ℝ, V))
    (hΨ : Tendsto Ψ atTop (𝓝 Ψ₀)) (z : V) (T : ℝ)
    (U : Set V) (hU : IsOpen U) (hseg : ∀ t ∈ Icc 0 T, Ψ₀ (z, t) ∈ U) :
    ∃ (Q : Set V) (B : ℕ → Set A) (ζ : ℕ → ℝ),
      IsCompact Q ∧ Q ⊆ U ∧
      (∀ᶠ r in atTop, ∀ t ∈ Icc 0 T, Ψ r (z, t) ∈ Q) ∧
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, 0 < ζ r) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => ((samples r : Measure A) (B r)).toReal) ∧
      (∀ r a, a ∈ B r → ∀ w ∈ Q, ‖(profile r a).val w - f.val w‖ < ζ r) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ a ∈ B r, ∀ t ∈ Icc 0 T,
        ‖(profile r a).val (Ψ r (z, t)) - f.val (Ψ₀ (z, t))‖ ≤ ζ r + η := by
  let K := ({z} : Set V) ×ˢ Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have himage : Ψ₀ '' K ⊆ U := by
    rintro _ ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
    have hwz : w = z := mem_singleton_iff.mp hw
    subst w
    exact hseg t ht
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hΨ) K hK
  obtain ⟨Q, hQ, hQU, _, hlate⟩ := exists_compact_eventual_flow_image hK
    Ψ₀.continuous.continuousOn hU himage hunif
  obtain ⟨B, ζ, hB, hζ, hζlim, hmass, hgood⟩ :=
    exists_good_sampled_profiles_sequence S Q hQ scale hscale samples profile hp ν hν hf
  have hZ : ∀ᶠ r in atTop, ∀ u ∈ K, Ψ r u ∈ Q := by
    filter_upwards [hlate] with r hr u hu
    exact hr (mem_image_of_mem _ hu)
  refine ⟨Q, B, ζ, hQ, hQU, ?_, hB, hζ, hζlim, hmass, hgood, ?_⟩
  · filter_upwards [hZ] with r hr t ht
    exact hr (z, t) ⟨mem_singleton z, ht⟩
  · intro η hη
    have hh := good_profile_along_flow f.val Ψ Ψ₀ hΨ K hK Q hZ
      (fun r a => (profile r a).val) B ζ (fun r a ha w hw => (hgood r a ha w hw).le) hη
    filter_upwards [hh] with r hr a ha t ht
    exact hr a ha (z, t) ⟨mem_singleton z, ht⟩

end PolycyclicRecognition

end

end OAI
