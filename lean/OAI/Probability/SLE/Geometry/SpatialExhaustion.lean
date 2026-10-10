import OAI.Probability.SLE.Geometry.BoundaryNull
import OAI.Probability.SLE.Gauge.CoverLimits

namespace OAI

/-! Removing the time and height cutoffs in the whole-trace upper bound. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

def interiorSpatialCutoff (R : ℝ) (n : ℕ) : Set ℂ :=
  closedBall 0 R ∩ {z | 1 / ((n : ℝ) + 1) ≤ z.im}

def compactTraceCutoff (γ : ℝ≥0 → ℂ) (R : ℝ) (n : ℕ) : Set ℂ :=
  interiorSpatialCutoff R n ∩ (γ '' Icc 0 (n : ℝ≥0))

lemma interiorSpatialCutoff_isCompact (R : ℝ) (n : ℕ) :
    IsCompact (interiorSpatialCutoff R n) :=
  (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const Complex.continuous_im)

lemma interiorSpatialCutoff_subset (R : ℝ) (n : ℕ) :
    interiorSpatialCutoff R n ⊆ upperHalfPlane ∩ closedBall 0 R := by
  intro z hz
  exact ⟨(by change 0 < z.im; exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans_le hz.2),
    hz.1⟩

lemma compactTraceCutoff_monotone (γ : ℝ≥0 → ℂ) (R : ℝ) :
    Monotone (compactTraceCutoff γ R) := by
  intro n m hnm z hz
  refine ⟨⟨hz.1.1, ?_⟩, ?_⟩
  · exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hnm 1 : (n : ℝ) + 1 ≤ (m : ℝ) + 1)).trans hz.1.2
  · exact image_mono (Icc_subset_Icc_right (Nat.cast_le.mpr hnm)) hz.2

lemma iUnion_compactTraceCutoff (γ : ℝ≥0 → ℂ) (R : ℝ) :
    (⋃ n, compactTraceCutoff γ R n) =
      wholeTrace γ ∩ closedBall 0 R ∩ upperHalfPlane := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact ⟨⟨image_subset_range _ _ hn.2, hn.1.1⟩,
      (interiorSpatialCutoff_subset R n hn.1).1⟩
  · rintro ⟨⟨⟨t, rfl⟩, hzR⟩, hzy⟩
    have hy : 0 < (γ t).im := hzy
    obtain ⟨n, hn⟩ := exists_nat_ge (max (t : ℝ) (1 / (γ t).im))
    have htn : t ≤ (n : ℝ≥0) := by
      exact_mod_cast (le_max_left _ _).trans hn
    have hprod : 1 ≤ (γ t).im * ((n : ℝ) + 1) := by
      have hdiv : 1 / (γ t).im ≤ (n : ℝ) + 1 :=
        (le_max_right _ _).trans (hn.trans (by linarith))
      simpa only [mul_comm] using (div_le_iff₀ hy).mp hdiv
    refine mem_iUnion.mpr ⟨n, ⟨hzR, ?_⟩, t, ⟨zero_le, htn⟩, rfl⟩
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr hprod

lemma sle_compact_trace_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h) (K : Set ℂ) (hK : IsClosed K)
    (s t : ℝ≥0) :
    AEMeasurable (fun ω => hausdorffGauge h (K ∩ (γ ω '' Icc s t))) P := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  let f : a.samples → C(ℝ≥0, ℂ) := fun ω => ⟨γ ω, a.trace_continuous ω⟩
  have hf : Measurable f := source_whole_path_measurable f
    (fun u => (hSLE.1 u).comp measurable_subtype_coe)
  have hm := (source_compact_trace_measure_measurable h hh K hK s t).comp hf
  have hemb : MeasurableEmbedding (Subtype.val : a.samples → Ω) :=
    MeasurableEmbedding.subtype_coe a.measurable_samples
  exact (a.measurePreserving_val.aemeasurable_comp_iff hemb).mp hm.aemeasurable

/-- Exhaustion by compact interior sets in the upper Hausdorff estimate
of Proposition `prop:dense-cover-upper`. -/
theorem whole_trace_expectation_of_compact_interior_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (hκ : 0 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) (R : ℝ) (C : ℝ≥0∞)
    (hcompact : ∀ (T : ℝ≥0) (K : Set ℂ), IsCompact K →
      K ⊆ upperHalfPlane ∩ closedBall 0 R →
      (∫⁻ ω, hausdorffGauge h (K ∩ (γ ω '' Icc 0 T)) ∂P) ≤ C) :
    (∫⁻ ω, hausdorffGauge h (wholeTrace (γ ω) ∩ closedBall 0 R) ∂P) ≤ C := by
  have hnull := explicit_gauge_real_axis_null hκ hh hf
  have heq : ∀ᵐ ω ∂P,
      hausdorffGauge h (wholeTrace (γ ω) ∩ closedBall 0 R) =
        hausdorffGauge h (⋃ n, compactTraceCutoff (γ ω) R n) := by
    obtain ⟨B, hB, htrace⟩ := hSLE.2
    filter_upwards [htrace] with ω hω
    obtain ⟨G, F, hw⟩ := hω
    rw [iUnion_compactTraceCutoff]
    apply measure_inter_eq_interior_of_null_boundary
    apply measure_mono_null (t := range ((↑) : ℝ → ℂ)) _ hnull
    rintro z ⟨⟨⟨t, rfl⟩, _⟩, hz⟩
    have hz0 : (γ ω t).im = 0 := le_antisymm (le_of_not_gt hz) (hw.2.2.1 t)
    refine ⟨(γ ω t).re, ?_⟩
    apply Complex.ext <;> simp [hz0]
  rw [lintegral_congr_ae heq]
  apply expected_measure_iUnion_le P (hausdorffGauge h)
    (fun n ω => compactTraceCutoff (γ ω) R n)
    (fun ω => compactTraceCutoff_monotone (γ ω) R)
  · intro n
    exact sle_compact_trace_aemeasurable P κ γ hSLE h hh
      (interiorSpatialCutoff R n) (interiorSpatialCutoff_isCompact R n).isClosed 0 n
  · intro n
    exact hcompact n (interiorSpatialCutoff R n)
      (interiorSpatialCutoff_isCompact R n) (interiorSpatialCutoff_subset R n)

/-- Compact interior upper estimates imply the whole-trace upper bound. -/
theorem mainConclusion_of_uniform_compact_interior_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ))
    (hcompact : ∀ R : ℝ, 0 < R → ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (T : ℝ≥0) (K : Set ℂ), IsCompact K →
        K ⊆ upperHalfPlane ∩ closedBall 0 R →
        (∫⁻ ω, hausdorffGauge h (K ∩ (γ ω '' Icc 0 T)) ∂P) ≤ C) :
    MainConclusion P h γ := by
  apply (mainConclusion_iff_finiteExpectedWholeTrace P κ hκ hκ8 γ hSLE h hh hf).mpr
  intro R hR
  obtain ⟨C, hC, hbound⟩ := hcompact R hR
  exact (whole_trace_expectation_of_compact_interior_bounds P κ hκ γ hSLE h hh hf
    R C hbound).trans_lt hC

end SLEExactGauge

end

end OAI
