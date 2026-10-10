import OAI.Probability.SLE.Geometry.RandomSpatialTesting

namespace OAI

/-! Local random spatial testing only needs almost-sure finite compact
masses. Infinite exceptional restrictions are set to zero measurably. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace SLEExactGauge

private lemma finite_restriction_version
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (K : Set X) (hK : MeasurableSet K) (hfin : ∀ᵐ ω ∂P, μ ω K < ∞) :
    ∃ ρ : Ω → Measure X, Measurable ρ ∧
      (∀ ω, IsFiniteMeasure (ρ ω)) ∧ ρ =ᵐ[P] (fun ω => (μ ω).restrict K) := by
  let ρ (ω : Ω) := if μ ω K < ∞ then (μ ω).restrict K else 0
  have hm : Measurable (fun ω => (μ ω).restrict K) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.restrict_apply hA]
    exact (Measure.measurable_coe (hA.inter hK)).comp hμ
  have hE : MeasurableSet {ω | μ ω K < ∞} :=
    measurableSet_lt ((Measure.measurable_coe hK).comp hμ) measurable_const
  refine ⟨ρ,hm.ite hE measurable_const,?_,?_⟩
  · intro ω
    dsimp only [ρ]
    split_ifs with hω
    · exact ⟨by simpa only [Measure.restrict_apply_univ] using hω⟩
    · infer_instance
  · filter_upwards [hfin] with ω hω
    exact ite_eq_left hω

private lemma bind_restrict_right
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (K : Set X) (hK : MeasurableSet K) :
    P.bind (fun ω => (μ ω).restrict K) = (P.bind μ).restrict K := by
  have hm : Measurable (fun ω => (μ ω).restrict K) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.restrict_apply hA]
    exact (Measure.measurable_coe (hA.inter hK)).comp hμ
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA hm.aemeasurable,Measure.restrict_apply hA,
    Measure.bind_apply (hA.inter hK) hμ.aemeasurable]
  simp only [Measure.restrict_apply hA]

theorem conditional_random_spatial_test_on_ae
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure X)
    (hμ : @Measurable Ω (Measure X) mΩ inferInstance μ)
    (hν : @Measurable Ω (Measure X) mΩ inferInstance ν)
    (K : Set X) (hK : MeasurableSet K)
    (hμK : ∀ᵐ ω ∂P, μ ω K < ∞) (hνK : ∀ᵐ ω ∂P, ν ω K < ∞)
    (hmean : P.bind μ K < ∞)
    (hevent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.restrict A).bind μ = (P.restrict A).bind ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod inferInstance) _ f) :
    ∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂μ ω ∂P =
      ∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂ν ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨ρ,hρ,hρfin,hρeq⟩ := finite_restriction_version P μ hμ K hK hμK
  obtain ⟨σ,hσ,hσfin,hσeq⟩ := finite_restriction_version P ν hν K hK hνK
  have hρbind (Q : Measure Ω) (he : ρ =ᵐ[Q] (fun ω => (μ ω).restrict K)) :
      Q.bind ρ = (Q.bind μ).restrict K :=
    (Measure.bind_congr_right he).trans (bind_restrict_right Q μ hμ K hK)
  have hσbind (Q : Measure Ω) (he : σ =ᵐ[Q] (fun ω => (ν ω).restrict K)) :
      Q.bind σ = (Q.bind ν).restrict K :=
    (Measure.bind_congr_right he).trans (bind_restrict_right Q ν hν K hK)
  have hρmean : P.bind ρ univ < ∞ := by
    rw [hρbind P hρeq,Measure.restrict_apply_univ]
    exact hmean
  have hE (A : Set Ω) (hA : MeasurableSet[m] A) :
      (P.restrict A).bind ρ = (P.restrict A).bind σ := by
    rw [hρbind _ hρeq.restrict,hσbind _ hσeq.restrict,hevent A hA]
  have h := conditional_random_spatial_test_finite m hm P ρ σ hρ hσ hρfin hσfin hρmean hE f hf
  calc
    (∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂μ ω ∂P) = ∫⁻ ω, ∫⁻ x, f (ω,x) ∂ρ ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hρeq] with ω hω
      rw [hω]
    _ = ∫⁻ ω, ∫⁻ x, f (ω,x) ∂σ ω ∂P := h
    _ = ∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂ν ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hσeq] with ω hω
      rw [hω]

end SLEExactGauge

end

end OAI
