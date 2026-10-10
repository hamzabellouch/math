import OAI.Analysis.CircleDomains.Selection.ExpectedWedges
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-!
# Joint integrability of the actual random wedge

Tonelli and the pointwise expected-wedge bound prove joint integrability.
Thus applying Fubini to the random staircase construction needs only
measurable input fields and the original integrable wedge majorant.
-/

open Set MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

/-- Finite squared norms of the original planar covectors make their
absolute wedge product integrable by Hölder's inequality. -/
theorem integrable_abs_planarWedge_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ × ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun z => |planarWedge (u z) (v z)|) μ := by
  have hu1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hu
  have hu2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hu
  have hv1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hv
  have hv2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hv
  have h12 : MemLp (fun z => (u z).1 * (v z).2) 1 μ := hu1.mul hv2
  have h21 : MemLp (fun z => (u z).2 * (v z).1) 1 μ := hu2.mul hv1
  exact ((memLp_one_iff_integrable.mp h12).sub (memLp_one_iff_integrable.mp h21)).abs

theorem integrable_nonnegative_prod_of_inner_bound
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f : A × B → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν))
    (h0 : ∀ p, 0 ≤ f p) (hi : ∀ y, Integrable (fun x => f (x, y)) μ)
    {b : B → ℝ} (hb : Integrable b ν)
    (hbound : ∀ y, (∫ x, f (x, y) ∂μ) ≤ b y) : Integrable f (μ.prod ν) := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).mpr ?_⟩
  rw [lintegral_prod_symm _ hf.aemeasurable.ennreal_ofReal]
  have hb0 : ∀ y, 0 ≤ b y := fun y =>
    (integral_nonneg (fun x => h0 (x, y))).trans (hbound y)
  calc
    _ = ∫⁻ y, ENNReal.ofReal (∫ x, f (x, y) ∂μ) ∂ν := by
      apply lintegral_congr
      intro y
      exact (ofReal_integral_eq_lintegral_ofReal (hi y)
        (Filter.Eventually.of_forall (fun x => h0 (x, y)))).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (b y) ∂ν :=
      lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hbound y))
    _ < ∞ := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hb0)).mp hb.2

/-- Every continuous two-shift integrand is integrable for the actual
compactly supported product shift law. -/
theorem integrable_shiftLaw_pair_of_continuous {h : ℝ} (hh : 0 < h)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f ((shiftLaw h).prod (shiftLaw h)) := by
  rw [shiftLaw_eq, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).smul_measure
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hh))
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hh)))

theorem measurable_staircaseCovector
    {Ω : Type*} [MeasurableSpace Ω] {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    {χ θ x : Ω → ℝ} {u c : Ω → ℝ × ℝ}
    (hχ : Measurable χ) (hθ : Measurable θ) (hx : Measurable x)
    (hu : Measurable u) (hc : Measurable c) :
    Measurable (fun ω => staircaseCovector h δ (χ ω) (θ ω) (x ω) (u ω) (c ω)) := by
  have hP := contDiff_smoothStaircase hh hδ hδh
  have hd : Measurable (deriv (smoothStaircase h δ)) :=
    (hP.continuous_deriv (by simp)).measurable
  have hv : Measurable (smoothStaircase h δ) := hP.continuous.measurable
  simp only [staircaseCovector, deriv_shiftedStaircase hh hδ hδh, shiftedStaircase]
  fun_prop

/-- Joint integrability follows from the original wedge and cutoff
terms; it is not assumed before interchanging the spatial and shift
integrals. -/
theorem integrable_staircase_pair_density
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hbound : Integrable (fun z => |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)) μ) :
    Integrable (fun p : (ℝ × ℝ) × X => |planarWedge
      (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
      (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|)
      (((shiftLaw h).prod (shiftLaw h)).prod μ) := by
  let := shiftLaw_isProbabilityMeasure hh
  let f : (ℝ × ℝ) × X → ℝ := fun p => |planarWedge
    (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
    (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|
  have hmu : Measurable (fun p : (ℝ × ℝ) × X =>
      staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2)) :=
    measurable_staircaseCovector hh hδ hδh
    (hχ.comp measurable_snd) (measurable_fst.fst) (hx.comp measurable_snd)
    (hu.comp measurable_snd) (hc.comp measurable_snd)
  have hmv : Measurable (fun p : (ℝ × ℝ) × X =>
      staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2)) :=
    measurable_staircaseCovector hh hδ hδh
    (hχ.comp measurable_snd) (measurable_fst.snd) (hy.comp measurable_snd)
    (hv.comp measurable_snd) (hc.comp measurable_snd)
  have hmf : Measurable f := ((hmu.fst.mul hmv.snd).sub (hmu.snd.mul hmv.fst)).abs
  refine integrable_nonnegative_prod_of_inner_bound hmf.aestronglyMeasurable
    (fun _ => abs_nonneg _) ?_ hbound ?_
  · intro z
    apply integrable_shiftLaw_pair_of_continuous hh
    exact (((continuous_staircaseCovector hh hδ hδh (χ z) (x z) (u z) (c z)).comp
      continuous_fst).fst.mul
      (((continuous_staircaseCovector hh hδ hδh (χ z) (y z) (v z) (c z)).comp
        continuous_snd).snd)).sub
        ((((continuous_staircaseCovector hh hδ hδh (χ z) (x z) (u z) (c z)).comp
          continuous_fst).snd).mul
          (((continuous_staircaseCovector hh hδ hδh (χ z) (y z) (v z) (c z)).comp
            continuous_snd).fst)) |>.abs
  · intro z
    rw [integral_shiftLaw_pair]
    simpa only [f, staircaseCovector] using
      average_staircase_wedge_le (u z) (v z) (c z) (x z) (y z)
      hh hδ hδh (hχ0 z) (hχ1 z)

end CircleDomainRigidity.FiniteTransfer

end OAI
