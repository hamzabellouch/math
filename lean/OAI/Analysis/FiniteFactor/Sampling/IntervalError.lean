import OAI.Analysis.FiniteFactor.Sampling.Smoothing

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Interval membership cannot change under a displacement smaller than
delta when the starting point is farther than delta from both endpoints. -/
theorem interval_membership_stable (a b δ t u : ℝ) (_hδ : 0 ≤ δ)
    (ha : δ < |t-a|) (hb : δ < |t-b|) (htu : |t-u| < δ) :
    u ∈ Set.Icc a b ↔ t ∈ Set.Icc a b := by
  have hd := abs_lt.mp htu
  constructor
  · intro hu
    constructor
    · by_contra ht
      have hh : t-a < 0 := by linarith
      rw [abs_of_neg hh] at ha
      linarith [hu.1]
    · by_contra ht
      have hh : 0 < t-b := by linarith
      rw [abs_of_pos hh] at hb
      linarith [hu.2]
  · intro ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at ha
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hb
    constructor <;> linarith

/-- A separated pair of representatives, with the first away from the cut,
has a fractional displacement outside the kernel's exceptional arc. -/
theorem fract_displacement_middle (δ t u : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ t) (ht' : t ≤ 1-δ) (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (hsep : δ ≤ |t-u|) : Int.fract (t-u) ∈ Set.Icc δ (1-δ) := by
  by_cases hpos : 0 ≤ t-u
  · rw [abs_of_nonneg hpos] at hsep
    rw [Int.fract_eq_self.mpr ⟨hpos, by linarith [hu.1]⟩]
    constructor <;> linarith [hu.1]
  · have hneg : t-u < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at hsep
    have hf : ⌊t-u⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith [hu.2], by norm_num; linarith⟩
    rw [Int.fract, hf]
    norm_num
    constructor <;> linarith [hu.2]

/-- The actual interval convolution differs from its indicator only by
the proved kernel tail, away from interval endpoints and the circle cut. -/
theorem samplingSmooth_interval_error (H : ℕ) (hH : 0 < H) (a b δ t : ℝ)
    (hδ : 0 < δ) (ht : δ ≤ t) (ht' : t ≤ 1-δ)
    (ha : δ < |t-a|) (hb : δ < |t-b|) :
    |samplingSmooth H (Set.Icc a b) t - (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t| ≤
      1/(4*(H : ℝ)*δ^2) := by
  let E := Set.Icc a b
  let K := fun u => samplingKernel H (t-u)
  let C := 1/(4*(H : ℝ)*δ^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hki : Integrable K unitIntervalMeasure :=
    ((samplingKernel_continuous H).comp (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hcut (B : Set ℝ) (hBm : MeasurableSet B)
      (hB : ∀ u ∈ B, ¬(u ∈ E ↔ t ∈ E)) :
      (∫ u in B, K u ∂unitIntervalMeasure) ≤ C := by
    rw [← integral_indicator hBm]
    have hle : ∀ᵐ u ∂unitIntervalMeasure, B.indicator K u ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
      by_cases hub : u ∈ B
      · rw [Set.indicator_of_mem hub]
        have hsep : δ ≤ |t-u| := by
          by_contra hh
          exact hB u hub (interval_membership_stable a b δ t u hδ.le ha hb (lt_of_not_ge hh))
        have hf := fract_displacement_middle δ t u hδ ht ht' hu hsep
        dsimp [K,C]
        rw [← samplingKernel_fract H (t-u)]
        exact samplingKernel_tail_bound H hH δ _ hδ hf.1 hf.2
      · rw [Set.indicator_of_notMem hub]
        exact hC
    have hh := integral_mono_ae (hki.indicator hBm) (integrable_const C) hle
    simpa using hh
  have hbounds := samplingSmooth_bounds H hH E t
  by_cases hte : t ∈ E
  · rw [Set.indicator_of_mem hte, abs_of_nonpos (by linarith [hbounds.2])]
    have hh := hcut Eᶜ measurableSet_Icc.compl (fun u hu he => hu (he.mpr hte))
    have hsplit := integral_add_compl (s := E) measurableSet_Icc hki
    have hone : (∫ u, K u ∂unitIntervalMeasure) = 1 := samplingKernel_shift_integral H hH t
    change (∫ u in E, K u ∂unitIntervalMeasure) + (∫ u in Eᶜ, K u ∂unitIntervalMeasure) = _ at hsplit
    change -(samplingSmooth H E t-1) ≤ C
    have heq : (∫ u in E, K u ∂unitIntervalMeasure) = samplingSmooth H E t := rfl
    rw [hone,heq] at hsplit
    linarith
  · rw [Set.indicator_of_notMem hte, sub_zero, abs_of_nonneg hbounds.1]
    exact hcut E measurableSet_Icc (fun u hu he => hte (he.mp hu))

end
end FiniteFactor

end OAI
