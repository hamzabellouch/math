import OAI.Analysis.KadisonSimilarity.Representation.DecomposableColumns

namespace OAI

/-! Diagonal indicator projections on the actual L² space and the pointwise
column bound for every operator in their commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (s : Set Ω) (hs : MeasurableSet s)

def l2Localize (f : Lp H 2 μ) : Lp H 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem l2Localize_ae (f : Lp H 2 μ) :
    l2Localize μ s hs f =ᵐ[μ] s.indicator f := MemLp.coeFn_toLp _

def l2LocalizationLinear : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := l2Localize μ s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [l2Localize_ae μ s hs (f + g), l2Localize_ae μ s hs f,
      l2Localize_ae μ s hs g, Lp.coeFn_add f g,
      Lp.coeFn_add (l2Localize μ s hs f) (l2Localize μ s hs g)] with a hfg hf hg hadd hout
    rw [hfg, hout]
    simp only [Pi.add_apply]
    rw [hf, hg]
    by_cases h : a ∈ s
    · simp only [Set.indicator_of_mem h]
      exact hadd
    · simp [h]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [l2Localize_ae μ s hs (c • f), l2Localize_ae μ s hs f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (l2Localize μ s hs f)] with a hcf hf hsmul hout
    change l2Localize μ s hs (c • f) a = (c • l2Localize μ s hs f) a
    rw [hcf, hout]
    simp only [Pi.smul_apply]
    rw [hf]
    by_cases h : a ∈ s <;> simp [h, hsmul]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem norm_l2Localize_le (f : Lp H 2 μ) : ‖l2Localize μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [l2Localize_ae μ s hs f] with a ha
  rw [ha]
  by_cases h : a ∈ s <;> simp [h]

def l2Localization : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (l2LocalizationLinear μ s hs).mkContinuous 1 (fun f => by
    change ‖l2Localize μ s hs f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_l2Localize_le μ s hs f)

omit [CompleteSpace H] in
theorem l2Localization_ae (f : Lp H 2 μ) :
    l2Localization μ s hs f =ᵐ[μ] s.indicator f := l2Localize_ae μ s hs f

variable [IsFiniteMeasure μ]

omit [CompleteSpace H] in
theorem l2Localization_const (x : H) :
    l2Localization μ s hs (Lp.const 2 μ x) = indicatorConstLp 2 hs (measure_ne_top μ s) x := by
  apply Lp.ext
  filter_upwards [l2Localization_ae μ s hs (Lp.const 2 μ x), Lp.coeFn_const 2 μ x,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := x)]
    with a hloc hc hi
  rw [hloc, hi]
  by_cases h : a ∈ s
  · simp only [Set.indicator_of_mem h]
    exact hc
  · simp [h]

omit [CompleteSpace H] in
/-- A genuine diagonal-commuting operator has pointwise bounded columns. -/
theorem diagonal_commutant_column_bound
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (x : H) : ∀ᵐ a ∂μ, ‖T (Lp.const 2 μ x) a‖ ≤ ‖T‖ * ‖x‖ := by
  apply decomposable_column_ae_bound μ T ?_ x
  intro r hr y
  have h := congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S (Lp.const 2 μ y)) (hT r hr)
  change T (l2Localization μ r hr (Lp.const 2 μ y)) =
    l2Localization μ r hr (T (Lp.const 2 μ y)) at h
  rw [l2Localization_const] at h
  rw [h]
  exact l2Localization_ae μ r hr (T (Lp.const 2 μ y))

end KadisonSimilarity

end

end OAI
