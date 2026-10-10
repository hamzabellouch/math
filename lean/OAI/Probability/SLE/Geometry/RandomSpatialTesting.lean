import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Deterministic spatial tests in an eventwise conditional measure identity
can be replaced by arbitrary nonnegative past-measurable spatial tests.
The proof compares the two joint measures on measurable rectangles. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace SLEExactGauge

private def pairedMeasure {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure X) (ω : Ω) : Measure (Ω × X) :=
  (μ ω).map (Prod.mk ω)

private lemma pairedMeasure_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure X) (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasure (μ ω)) :
    Measurable (pairedMeasure μ) := by
  let κ : Kernel Ω X := ⟨μ,hμ⟩
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have h := Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hA hfin
  simpa only [pairedMeasure,Measure.map_apply measurable_prodMk_left hA] using (show Measurable (fun a => μ a (Prod.mk a ⁻¹' A)) from h)

private lemma pairedMeasure_rectangle
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (A : Set Ω) (hA : MeasurableSet A) (K : Set X) (hK : MeasurableSet K) :
    P.bind (pairedMeasure μ) (A ×ˢ K) = (P.restrict A).bind μ K := by
  rw [Measure.bind_apply (hA.prod hK) (pairedMeasure_measurable μ hμ hfin).aemeasurable,
    Measure.bind_apply hK hμ.aemeasurable]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro ω
  rw [pairedMeasure,Measure.map_apply measurable_prodMk_left (hA.prod hK)]
  by_cases hω : ω ∈ A <;> simp [hω]

private lemma pairedMeasure_lintegral
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (f : Ω × X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p ∂P.bind (pairedMeasure μ) = ∫⁻ ω, ∫⁻ x, f (ω,x) ∂μ ω ∂P := by
  rw [Measure.lintegral_bind (pairedMeasure_measurable μ hμ hfin).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro ω
  exact lintegral_map hf measurable_prodMk_left

private lemma finite_spatial_test_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure X) (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (f : Ω × X → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ x, f (ω,x) ∂μ ω) := by
  have h := (Measure.measurable_lintegral hf).comp (pairedMeasure_measurable μ hμ hfin)
  convert h using 1
  funext ω
  exact (lintegral_map hf measurable_prodMk_left).symm

private lemma measurable_measure_restrict
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Ω → Measure X) (hμ : Measurable μ) (K : Set X) (hK : MeasurableSet K) :
    Measurable (fun ω => (μ ω).restrict K) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [Measure.restrict_apply hA]
  exact (Measure.measurable_coe (hA.inter hK)).comp hμ

/-- Finite mean kernels that agree after restriction to every past event
agree on every nonnegative joint past/spatial test. Pointwise masses may be
unbounded; only their total mean must be finite. -/
theorem conditional_random_spatial_test_finite
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure X)
    (hμ : @Measurable Ω (Measure X) mΩ inferInstance μ)
    (hν : @Measurable Ω (Measure X) mΩ inferInstance ν)
    (hμfin : ∀ ω, IsFiniteMeasure (μ ω)) (hνfin : ∀ ω, IsFiniteMeasure (ν ω))
    (hmean : P.bind μ univ < ∞)
    (hevent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.restrict A).bind μ = (P.restrict A).bind ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod inferInstance) _ f) :
    ∫⁻ ω, ∫⁻ x, f (ω,x) ∂μ ω ∂P = ∫⁻ ω, ∫⁻ x, f (ω,x) ∂ν ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hprod : m.prod (inferInstance : MeasurableSpace X) ≤
      mΩ.prod (inferInstance : MeasurableSpace X) :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  let Jμ := P.bind (pairedMeasure μ)
  let Jν := P.bind (pairedMeasure ν)
  have hJfin : IsFiniteMeasure Jμ := by
    constructor
    have he := pairedMeasure_rectangle P μ hμ hμfin univ MeasurableSet.univ univ MeasurableSet.univ
    have hvalue : Jμ univ = P.bind μ univ := by
      simpa only [univ_prod_univ,Measure.restrict_univ,Jμ] using he
    rw [hvalue]
    exact hmean
  let : IsFiniteMeasure Jμ := hJfin
  have hrect (A : Set Ω) (K : Set X) (hA : MeasurableSet[m] A) (hK : MeasurableSet K) :
      Jμ.trim hprod (A ×ˢ K) = Jν.trim hprod (A ×ˢ K) := by
    rw [trim_measurableSet_eq hprod (hA.prod hK),
      trim_measurableSet_eq hprod (hA.prod hK)]
    rw [pairedMeasure_rectangle P μ hμ hμfin A (hm _ hA) K hK,
      pairedMeasure_rectangle P ν hν hνfin A (hm _ hA) K hK,hevent A hA]
  have heq : Jμ.trim hprod = Jν.trim hprod := by
    let : MeasurableSpace Ω := m
    apply Measure.ext_prod
    intro A K hA hK
    exact hrect A K hA hK
  have hf' : Measurable f := hf.mono hprod le_rfl
  rw [← pairedMeasure_lintegral P μ hμ hμfin f hf',
    ← pairedMeasure_lintegral P ν hν hνfin f hf']
  rw [← lintegral_trim hprod hf,← lintegral_trim hprod hf,heq]

/-- A local version for a fixed finite spatial set, suitable for compact
restrictions of locally finite random Radon measures. -/
theorem conditional_random_spatial_test_on
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure X)
    (hμ : @Measurable Ω (Measure X) mΩ inferInstance μ)
    (hν : @Measurable Ω (Measure X) mΩ inferInstance ν)
    (K : Set X) (hK : MeasurableSet K)
    (hμK : ∀ ω, μ ω K < ∞) (hνK : ∀ ω, ν ω K < ∞)
    (hmean : P.bind μ K < ∞)
    (hevent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.restrict A).bind μ = (P.restrict A).bind ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod inferInstance) _ f) :
    ∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂μ ω ∂P =
      ∫⁻ ω, ∫⁻ x in K, f (ω,x) ∂ν ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hμr := measurable_measure_restrict μ hμ K hK
  have hνr := measurable_measure_restrict ν hν K hK
  have hμfin (ω : Ω) : IsFiniteMeasure ((μ ω).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμK ω⟩
  have hνfin (ω : Ω) : IsFiniteMeasure ((ν ω).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hνK ω⟩
  have hmr : P.bind (fun ω => (μ ω).restrict K) univ < ∞ := by
    rw [Measure.bind_apply MeasurableSet.univ hμr.aemeasurable]
    simp only [Measure.restrict_apply_univ]
    rwa [Measure.bind_apply hK hμ.aemeasurable] at hmean
  apply conditional_random_spatial_test_finite m hm P _ _ hμr hνr hμfin hνfin hmr _ f hf
  intro A hA
  apply Measure.ext
  intro S hS
  rw [Measure.bind_apply hS hμr.aemeasurable,Measure.bind_apply hS hνr.aemeasurable]
  simp only [Measure.restrict_apply hS]
  rw [← Measure.bind_apply (hS.inter hK) hμ.aemeasurable,
    ← Measure.bind_apply (hS.inter hK) hν.aemeasurable,hevent A hA]

/-- Countably many finite-mean spatial pieces suffice; neither random
measure needs finite mass on the entire space. -/
theorem conditional_random_spatial_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (P : @Measure Ω mΩ)
    (μ ν : Ω → Measure X)
    (hμ : @Measurable Ω (Measure X) mΩ inferInstance μ)
    (hν : @Measurable Ω (Measure X) mΩ inferInstance ν)
    (K : ℕ → Set X) (hKm : ∀ n, MeasurableSet (K n))
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) (hcover : ⋃ n, K n = univ)
    (hμK : ∀ n ω, μ ω (K n) < ∞) (hνK : ∀ n ω, ν ω (K n) < ∞)
    (hmean : ∀ n, P.bind μ (K n) < ∞)
    (hevent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.restrict A).bind μ = (P.restrict A).bind ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod inferInstance) _ f) :
    ∫⁻ ω, ∫⁻ x, f (ω,x) ∂μ ω ∂P = ∫⁻ ω, ∫⁻ x, f (ω,x) ∂ν ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hprod : m.prod (inferInstance : MeasurableSpace X) ≤
      mΩ.prod (inferInstance : MeasurableSpace X) :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  have hf' : Measurable f := hf.mono hprod le_rfl
  have hparts (n : ℕ) := conditional_random_spatial_test_on m hm P μ ν hμ hν
    (K n) (hKm n) (hμK n) (hνK n) (hmean n) hevent f hf
  have hmeas (ρ : Ω → Measure X) (hr : Measurable ρ)
      (hfinite : ∀ n ω, ρ ω (K n) < ∞) (n : ℕ) :
      Measurable (fun ω => ∫⁻ x in K n, f (ω,x) ∂ρ ω) := by
    apply finite_spatial_test_measurable _ (measurable_measure_restrict ρ hr _ (hKm n)) _ f hf'
    intro ω
    exact ⟨by simpa only [Measure.restrict_apply_univ] using hfinite n ω⟩
  have hsplit (ρ : Ω → Measure X) (ω : Ω) :
      (∫⁻ x, f (ω,x) ∂ρ ω) = ∑' n, ∫⁻ x in K n, f (ω,x) ∂ρ ω := by
    simpa only [hcover,Measure.restrict_univ] using lintegral_iUnion hKm hdis (fun x => f (ω,x))
  simp_rw [hsplit]
  rw [lintegral_tsum (fun n => (hmeas μ hμ hμK n).aemeasurable),
    lintegral_tsum (fun n => (hmeas ν hν hνK n).aemeasurable)]
  simp_rw [hparts]

end SLEExactGauge

end

end OAI
