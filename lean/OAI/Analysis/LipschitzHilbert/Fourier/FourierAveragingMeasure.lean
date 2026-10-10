import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingKernel
import Mathlib.MeasureTheory.Measure.WithDensityFinite

namespace OAI

/-!
# An actual Fourier-supported averaging probability

Normalize the positive Fourier-square kernel and instantiate its compact
frequency bump. This constructs a probability satisfying `FourierGap` for
every positive gap, rather than assuming existence of an averaging law.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

open PhaseCombinatorics

def fourierAveragingDensity (h : SchwartzMap ℝ ℂ) (t : ℝ) : ℝ :=
  fourierSquare h t / ∫ x, fourierSquare h x

def fourierAveragingMeasure (h : SchwartzMap ℝ ℂ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (fourierAveragingDensity h t))

theorem fourierAveragingDensity_nonneg (h : SchwartzMap ℝ ℂ) (t : ℝ) :
    0 ≤ fourierAveragingDensity h t :=
  div_nonneg (fourierSquare_nonneg h t) (integral_nonneg (fourierSquare_nonneg h))

theorem fourierAveragingDensity_continuous (h : SchwartzMap ℝ ℂ) :
    Continuous (fourierAveragingDensity h) := (fourierSquare_continuous h).div_const _

theorem fourierAveragingDensity_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fourierAveragingDensity h) := (fourierSquare_integrable h).div_const _

theorem fourierAveragingDensity_integral (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    (∫ t, fourierAveragingDensity h t) = 1 := by
  unfold fourierAveragingDensity
  rw [integral_div, div_self (fourierSquare_mass_pos h hx).ne']

theorem fourierAveragingMeasure_isProbability (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    IsProbabilityMeasure (fourierAveragingMeasure h) := by
  constructor
  unfold fourierAveragingMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (fourierAveragingDensity_integrable h)
      (Filter.Eventually.of_forall (fourierAveragingDensity_nonneg h)),
    fourierAveragingDensity_integral h hx, ENNReal.ofReal_one]

/-- Fourier moments of the probability are the normalized kernel moments. -/
theorem fourierAveragingMeasure_moment (h : SchwartzMap ℝ ℂ) (s : ℝ) :
    fourierMoment (fourierAveragingMeasure h) s =
      ((∫ x, fourierSquare h x : ℝ) : ℂ)⁻¹ *
        ∫ t, (fourierSquare h t : ℂ) * character s t := by
  unfold fourierMoment fourierAveragingMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((fourierAveragingDensity_continuous h).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (fourierAveragingDensity_nonneg h _)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [fourierAveragingDensity, Complex.real_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- A bump of radius `r` gives a probability with the required Fourier gap
whenever `16πr ≤ gap`. -/
theorem fourierAveragingMeasure_fourierGap (h : SchwartzMap ℝ ℂ) {r gap : ℝ}
    (hsupport : ∀ x, r ≤ |x| → h x = 0) (hband : 16 * Real.pi * r ≤ gap) :
    FourierGap (fourierAveragingMeasure h) gap := by
  intro s hs
  let a := s / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  have ha : 2 * r ≤ |a| := by
    dsimp only [a]
    rw [abs_div, abs_of_pos hpi]
    apply (le_div_iff₀ hpi).2
    nlinarith
  have heq : 2 * Real.pi * a = s := by dsimp only [a]; field_simp
  rw [fourierAveragingMeasure_moment, ← heq,
    fourierSquare_moment_eq_zero h hsupport ha, mul_zero]

/-- A genuine compactly supported smooth bump for the kernel construction. -/
theorem exists_compact_frequency_bump {r : ℝ} (hr : 0 < r) :
    ∃ h : SchwartzMap ℝ ℂ, h 0 ≠ 0 ∧ ∀ x, r ≤ |x| → h x = 0 := by
  have hnhds : Set.Ioo (-r) r ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩
  obtain ⟨f, hsupp, hcompact, hsmooth, _, hzero⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hnhds
  let h : SchwartzMap ℝ ℂ :=
    (hcompact.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hsmooth)
  refine ⟨h, ?_, ?_⟩
  · change (f 0 : ℂ) ≠ 0
    rw [hzero]
    norm_num
  · intro x hx
    have hf : f x = 0 := by
      by_contra hfx
      have hmem : x ∈ tsupport f := subset_closure (show x ∈ Function.support f from hfx)
      have hlt : |x| < r := abs_lt.mpr (hsupp hmem)
      exact not_lt_of_ge hx hlt
    change (f x : ℂ) = 0
    rw [hf, Complex.ofReal_zero]

/-- Every positive gap admits an explicitly constructed averaging probability
with smooth nonnegative density and exactly vanishing outside moments. -/
theorem exists_fourierAveragingMeasure {gap : ℝ} (hgap : 0 < gap) :
    ∃ h : SchwartzMap ℝ ℂ, h 0 ≠ 0 ∧
      IsProbabilityMeasure (fourierAveragingMeasure h) ∧
      FourierGap (fourierAveragingMeasure h) gap := by
  let r := gap / (16 * Real.pi)
  have hr : 0 < r := div_pos hgap (by positivity)
  obtain ⟨h, hh, hsupport⟩ := exists_compact_frequency_bump hr
  refine ⟨h, hh, fourierAveragingMeasure_isProbability h hh,
    fourierAveragingMeasure_fourierGap h hsupport ?_⟩
  dsimp only [r]
  have hpi : 16 * Real.pi ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hpi]

end LipschitzHilbert

end

end OAI
