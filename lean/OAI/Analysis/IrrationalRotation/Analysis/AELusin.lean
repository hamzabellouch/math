import OAI.Analysis.IrrationalRotation.Analysis.StrongLusin

namespace OAI

open Set MeasureTheory Topology
open scoped ENNReal

namespace Invariant233.SimultaneousLusin

theorem exists_compact_continuousOn_of_ae {X Y : Type*}
    [t : TopologicalSpace X] [hPolish : PolishSpace X]
    [m : MeasurableSpace X] [hBorel : BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {p : X → Prop}
    (hp : ∀ᵐ x ∂μ, p x) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧
      ContinuousOn f K ∧ ∀ x ∈ K, p x := by
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  obtain ⟨t', hle, hfc, hP'⟩ := hf.exists_continuous
  have hB' : @BorelSpace X t' m := by
    constructor
    exact hBorel.measurable_eq.trans
      (MeasureTheory.borel_eq_borel_of_le hP' hPolish hle).symm
  let : TopologicalSpace X := t'
  let : PolishSpace X := hP'
  let : BorelSpace X := hB'
  obtain ⟨K, hKsub, hK, hsmall⟩ :=
    hNm.compl.exists_isCompact_sdiff_lt (measure_ne_top μ Nᶜ) hε
  have hKold : @IsCompact X t K := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  refine ⟨K, hKold, ?_, ?_, ?_⟩
  · have heq : Nᶜ \ K = Kᶜ \ N := by ext x; simp [and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hsmall
  · exact @continuousOn_of_finer_compact X Y t inferInstance _ t' hle K hK f hfc
  · intro x hx
    by_contra hn
    exact hKsub hx (hNsub hn)

theorem exists_compact_continuousOn_of_aemeasurable {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : AEMeasurable f μ) {p : X → Prop}
    (hp : ∀ᵐ x ∂μ, p x) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧
      ContinuousOn f K ∧ ∀ x ∈ K, p x := by
  obtain ⟨K, hK, hsmall, hcont, hgood⟩ :=
    exists_compact_continuousOn_of_ae μ hf.measurable_mk (hp.and hf.ae_eq_mk) hε
  exact ⟨K, hK, hsmall, hcont.congr (fun x hx => (hgood x hx).2),
    fun x hx => (hgood x hx).1⟩

end Invariant233.SimultaneousLusin

namespace Invariant233.StrongLusin

theorem exists_compact_strong_and_continuousOn_of_ae {𝕜 X E F ι J : Type*}
    {Y : J → Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [∀ j, TopologicalSpace (Y j)] [∀ j, MeasurableSpace (Y j)]
    [∀ j, OpensMeasurableSpace (Y j)] [∀ j, SecondCountableTopology (Y j)]
    [Countable ι] [Countable J] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, AEMeasurable (fun x => A x (b i)) μ)
    (g : ∀ j, X → Y j) (hg : ∀ j, AEMeasurable (g j) μ)
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      (∀ v : E, ContinuousOn (fun x => A x v) Q) ∧
      (∀ j, ContinuousOn (g j) Q) ∧
      ∀ x ∈ Q, p x ∧ ‖A x‖ ≤ C := by
  have hmeas : AEMeasurable (fun x => ((fun i => A x (b i)), (fun j => g j x))) μ :=
    (AEMeasurable.of_eval hcolumns).prodMk (AEMeasurable.of_eval hg)
  obtain ⟨Q, hQ, hsmall, hcont, hgood⟩ :=
    SimultaneousLusin.exists_compact_continuousOn_of_aemeasurable μ hmeas (hp.and hbound) hε
  refine ⟨Q, hQ, hsmall, ?_, continuousOn_pi.mp hcont.snd, hgood⟩
  exact fun v => StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
    (fun x hx => (hgood x hx).2) b (continuousOn_pi.mp hcont.fst) v

end Invariant233.StrongLusin

end OAI
