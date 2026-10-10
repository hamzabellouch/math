import OAI.Probability.SLE.Mass.RadonRandomTesting
import OAI.Probability.SLE.Mass.RadonTestFamily

namespace OAI

/-! Random spatial testing for conditional kernels of locally finite
half-plane measures, allowing exceptional non-locally-finite values. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped ENNReal

namespace SLEExactGauge

local instance conditionalTestLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

private lemma locallyFiniteKernelVersion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (μ ω)) :
    ∃ ρ : Ω → Measure upperHalfPlane, Measurable ρ ∧
      (∀ ω, IsFiniteMeasureOnCompacts (ρ ω)) ∧ ρ =ᵐ[P] μ := by
  let D := localTestFamily upperHalfPlane
  let E := {ω | ∀ n, μ ω (D.compactSet n) < ∞}
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    simpa only [Function.comp_def] using measurableSet_lt
      ((Measure.measurable_coe (D.isCompact n).measurableSet).comp hμ)
      (measurable_const : Measurable (fun _ : Ω => (∞:ℝ≥0∞)))
  let ρ (ω : Ω) := if ω ∈ E then μ ω else 0
  refine ⟨ρ,hμ.ite hE measurable_const,?_,?_⟩
  · intro ω
    by_cases hω : ω ∈ E
    · have he : ρ ω=μ ω := ite_eq_left hω
      rw [he]
      constructor
      intro K hK
      obtain ⟨n,hn⟩ := D.exhaustive K hK
      exact lt_of_le_of_lt (measure_mono hn) (hω n)
    · simp only [ρ,ite_eq_right hω]
      infer_instance
  · filter_upwards [hfin] with ω hω
    have : ω ∈ E := fun n => by let := hω; exact (D.isCompact n).measure_lt_top
    exact ite_eq_left this

lemma ae_finite_on_compacts_of_compact_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hmean : ∀ K : Set upperHalfPlane, IsCompact K → P.bind μ K < ∞) :
    ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (μ ω) := by
  let D := localTestFamily upperHalfPlane
  have hfin (n : ℕ) : ∀ᵐ ω ∂P, μ ω (D.compactSet n) < ∞ := by
    apply ae_lt_top ((Measure.measurable_coe (D.isCompact n).measurableSet).comp hμ)
    change (∫⁻ ω, μ ω (D.compactSet n) ∂P) ≠ ∞
    rw [← Measure.bind_apply (D.isCompact n).measurableSet hμ.aemeasurable]
    exact (hmean _ (D.isCompact n)).ne
  filter_upwards [ae_all_iff.mpr hfin] with ω hω
  constructor
  intro K hK
  obtain ⟨n,hn⟩ := D.exhaustive K hK
  exact lt_of_le_of_lt (measure_mono hn) (hω n)

/-- Equality of conditional mean measures gives arbitrary jointly
past-measurable tests. Only compact mean masses need be finite. -/
theorem conditional_halfPlane_random_test
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure upperHalfPlane) (hμ : Measurable[mΩ] μ) (hν : Measurable[mΩ] ν)
    (hμfin : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (μ ω))
    (hνfin : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (ν ω))
    (hmean : ∀ K : Set upperHalfPlane, IsCompact K → P.bind μ K < ∞)
    (hevent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.restrict A).bind μ=(P.restrict A).bind ν)
    (f : Ω × upperHalfPlane → ℝ≥0∞) (hf : Measurable[m.prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ z, f (ω,z) ∂μ ω ∂P) = ∫⁻ ω, ∫⁻ z, f (ω,z) ∂ν ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨ρ,hρ,hρfin,hρeq⟩ := locallyFiniteKernelVersion P μ hμ hμfin
  obtain ⟨σ,hσ,hσfin,hσeq⟩ := locallyFiniteKernelVersion P ν hν hνfin
  let D := localTestFamily upperHalfPlane
  have hE (A : Set Ω) (hA : MeasurableSet[m] A) :
      (P.restrict A).bind ρ=(P.restrict A).bind σ := by
    rw [Measure.bind_congr_right (ae_restrict_of_ae hρeq),
      Measure.bind_congr_right (ae_restrict_of_ae hσeq),hevent A hA]
  have hcov : ⋃ n, disjointed D.compactSet n=univ := by
    rw [iUnion_disjointed]
    apply eq_univ_iff_forall.mpr
    intro z
    obtain ⟨n,hn⟩ := D.exhaustive {z} isCompact_singleton
    exact mem_iUnion.mpr ⟨n,hn (mem_singleton z)⟩
  have hρK (n : ℕ) (ω : Ω) : ρ ω (disjointed D.compactSet n) < ∞ := by
    let := hρfin ω
    exact lt_of_le_of_lt (measure_mono (disjointed_subset D.compactSet n))
      (D.isCompact n).measure_lt_top
  have hσK (n : ℕ) (ω : Ω) : σ ω (disjointed D.compactSet n) < ∞ := by
    let := hσfin ω
    exact lt_of_le_of_lt (measure_mono (disjointed_subset D.compactSet n))
      (D.isCompact n).measure_lt_top
  have hmeanρ (n : ℕ) : P.bind ρ (disjointed D.compactSet n) < ∞ := by
    rw [Measure.bind_congr_right hρeq]
    exact lt_of_le_of_lt (measure_mono (disjointed_subset D.compactSet n))
      (hmean _ (D.isCompact n))
  have h := conditional_random_spatial_test m hm P ρ σ hρ hσ
    (disjointed D.compactSet) (MeasurableSet.disjointed fun n => (D.isCompact n).measurableSet)
    (disjoint_disjointed D.compactSet) hcov hρK hσK hmeanρ hE f hf
  calc
    _ = ∫⁻ ω, ∫⁻ z, f (ω,z) ∂ρ ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hρeq] with ω hω
      rw [hω]
    _ = ∫⁻ ω, ∫⁻ z, f (ω,z) ∂σ ω ∂P := h
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hσeq] with ω hω
      rw [hω]

end SLEExactGauge

end

end OAI
