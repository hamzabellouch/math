import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierSubLeft
import OAI.MeasureTheory.FalconerCompletion.Fourier.PolynomialKernel
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift2

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section PolynomialFourierSmoothing
open scoped FourierTransform
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_polynomial_smoothing (χ : SchwartzMap V ℂ) {p : ℕ}
    (hp : Module.finrank ℝ V < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure V), IsProbabilityMeasure μ →
      (∀ᵐ x ∂μ, χ x = 1) → ∀ v : V,
      ‖PlanarFalconer.sourceFourier μ v‖^2 ≤
        C * ∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖^2 *
          polynomialKernel p (v-u) := by
  obtain ⟨D,hD,hdecay⟩ := schwartz_le_polynomialKernel (𝓕 χ : SchwartzMap V ℂ) p
  let J : ℝ := ∫ z : V, ‖(𝓕 χ : SchwartzMap V ℂ) z‖
  have hJ : 0 ≤ J := integral_nonneg (fun z => norm_nonneg _)
  refine ⟨1 + J*D, by positivity, ?_⟩
  intro μ hμ hχ v
  let := hμ
  have hf : Continuous (fun u : V => ‖PlanarFalconer.sourceFourier μ u‖^2) := by
    unfold PlanarFalconer.sourceFourier
    fun_prop
  have hf1 (u : V) : ‖PlanarFalconer.sourceFourier μ u‖^2 ≤ 1 := by
    simpa only [PlanarFalconer.sourceFourier, one_pow] using
      pow_le_pow_left₀ (norm_nonneg _)
      (norm_charFun_le_one (μ := μ) ((-(2*Real.pi)) • u)) 2
  have hk := (polynomialKernel_integrable (V := V) hp).comp_sub_left v
  have hi : Integrable (fun u : V => ‖PlanarFalconer.sourceFourier μ u‖^2 *
      polynomialKernel p (v-u)) := by
    apply hk.mono' (hf.mul ((continuous_polynomialKernel p).comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
    filter_upwards with u
    change ‖‖PlanarFalconer.sourceFourier μ u‖^2 * polynomialKernel p (v-u)‖ ≤
      polynomialKernel p (v-u)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (polynomialKernel_pos p _).le)]
    exact mul_le_of_le_one_left (polynomialKernel_pos p _).le (hf1 u)
  have hmajor : (∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖^2 * ‖(𝓕 χ) (v-u)‖) ≤
      D * ∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖^2 * polynomialKernel p (v-u) := by
    have hh := integral_mono_of_nonneg
      (ae_of_all volume (fun u : V => mul_nonneg (sq_nonneg _) (norm_nonneg _)))
      (hi.const_mul D)
      (ae_of_all volume (fun u : V => show
        ‖PlanarFalconer.sourceFourier μ u‖^2 * ‖(𝓕 χ) (v-u)‖ ≤
          D * (‖PlanarFalconer.sourceFourier μ u‖^2 * polynomialKernel p (v-u)) from by
            have h := mul_le_mul_of_nonneg_left (hdecay (v-u)) (sq_nonneg
              ‖PlanarFalconer.sourceFourier μ u‖)
            simpa only [mul_left_comm] using h))
    simpa only [integral_const_mul] using hh
  have hh := (sourceFourier_sq_le_smooth μ χ hχ v).trans
    (mul_le_mul_of_nonneg_left hmajor hJ)
  have hnonneg : 0 ≤ ∫ u : V, ‖PlanarFalconer.sourceFourier μ u‖^2 *
      polynomialKernel p (v-u) := integral_nonneg
        (fun u => mul_nonneg (sq_nonneg _) (polynomialKernel_pos p _).le)
  dsimp only [J] at *
  nlinarith

omit [FiniteDimensional ℝ V] [BorelSpace V] in

theorem sourceFourier_norm_le_one (μ : Measure V) [IsProbabilityMeasure μ] (u : V) :
    ‖PlanarFalconer.sourceFourier μ u‖ ≤ 1 := by
  exact norm_charFun_le_one (μ := μ) ((-(2*Real.pi)) • u)

theorem sourceFourier_annular_integral (χ : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ν : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ν → (∀ᵐ x ∂μ, χ x = 1) →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ x : V, ν (Metric.ball x 1) ≤ ENNReal.ofReal A) →
      ν Set.univ ≤ ENNReal.ofReal (2*B) →
      (∀ᵐ x ∂ν, ‖x‖ ≤ 2*B) →
      (∫ v : V, ‖PlanarFalconer.sourceFourier μ v‖^2 ∂ν) ≤
        C * (A * ∫ u : V in Metric.ball 0 (4*B),
          ‖PlanarFalconer.sourceFourier μ u‖^2) + C := by
  let p := Module.finrank ℝ V + 1
  have hp : Module.finrank ℝ V < p := by omega
  have hp1 : Module.finrank ℝ V < p+1 := by omega
  obtain ⟨C₀,hC₀,hsmooth⟩ := sourceFourier_polynomial_smoothing χ hp1
  let J : ℝ := (2^(p+1) / volume.real (Metric.ball (0 : V) 1)) *
    ∫ z : V, polynomialKernel (p+1) z
  let T : ℝ := 2^(p+2) * ∫ z : V, polynomialKernel p z
  have hJ : 0 ≤ J := mul_nonneg (div_nonneg (by positivity) measureReal_nonneg)
    (integral_nonneg (fun z => (polynomialKernel_pos (p+1) z).le))
  have hT : 0 ≤ T := mul_nonneg (by positivity)
    (integral_nonneg (fun z => (polynomialKernel_pos p z).le))
  refine ⟨C₀ * (1+J+T), by positivity, ?_⟩
  intro μ ν hμ hν hχ A B hA hB hball hmass hsupp
  let := hμ
  let := hν
  let f : V → ℝ := fun u => ‖PlanarFalconer.sourceFourier μ u‖^2
  have hf : Continuous f := by unfold f PlanarFalconer.sourceFourier; fun_prop
  have hf0 (u : V) : 0 ≤ f u := sq_nonneg _
  have hf1 (u : V) : f u ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (sourceFourier_norm_le_one μ u) 2
  have hfn (u : V) : ‖f u‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hf0 u)]
    exact hf1 u
  have hi := bounded_mul_polynomialKernel_integrable_prod ν hp1 f hf hfn
  have hw := hi.integral_prod_left
  have hswap := integral_integral_swap (f := fun v u : V =>
    f u * polynomialKernel (p+1) (v-u)) hi
  let W : V → ℝ := fun u => ∫ v : V, polynomialKernel (p+1) (v-u) ∂ν
  have hW (u : V) : W u = ∫ v : V, polynomialKernel (p+1) (u-v) ∂ν := by
    apply integral_congr_ae
    filter_upwards with v
    simp only [polynomialKernel, norm_sub_rev]
  have hW0 (u : V) : 0 ≤ W u := integral_nonneg
    (fun v => (polynomialKernel_pos (p+1) (v-u)).le)
  have hWball (u : V) : W u ≤ J*A := by
    rw [hW]
    convert polynomialKernel_integral_le ν hp1 hA hball u using 1
    dsimp only [J]
    ring
  have hWtail (u : V) (hu : u ∉ Metric.ball (0 : V) (4*B)) :
      W u ≤ 2^(p+2) * polynomialKernel p u := by
    rw [hW]
    apply polynomialKernel_annular_tail ν p hB hmass hsupp u
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hu
  have hfi : IntegrableOn f (Metric.ball (0 : V) (4*B)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : V) (4*B))).mono_set
      Metric.ball_subset_closedBall
  have hmajori : Integrable (fun u : V =>
      J*A * (Metric.ball (0 : V) (4*B)).indicator f u +
        2^(p+2) * polynomialKernel p u) :=
    ((hfi.integrable_indicator measurableSet_ball).const_mul (J*A)).add
      ((polynomialKernel_integrable hp).const_mul (2^(p+2)))
  have hmajor (u : V) : f u * W u ≤
      J*A * (Metric.ball (0 : V) (4*B)).indicator f u +
        2^(p+2) * polynomialKernel p u := by
    by_cases hu : u ∈ Metric.ball (0 : V) (4*B)
    · rw [Set.indicator_of_mem hu]
      have hh := mul_le_mul_of_nonneg_left (hWball u) (hf0 u)
      have hn : 0 ≤ (2:ℝ)^(p+2) * polynomialKernel p u :=
        mul_nonneg (by positivity) (polynomialKernel_pos p u).le
      nlinarith
    · rw [Set.indicator_of_notMem hu, mul_zero, zero_add]
      exact (mul_le_of_le_one_left (hW0 u) (hf1 u)).trans (hWtail u hu)
  have hglobal := integral_mono_of_nonneg
    (ae_of_all volume (fun u => mul_nonneg (hf0 u) (hW0 u))) hmajori
    (ae_of_all volume hmajor)
  rw [integral_add ((hfi.integrable_indicator measurableSet_ball).const_mul (J*A))
      ((polynomialKernel_integrable hp).const_mul (2^(p+2))), integral_const_mul,
    integral_const_mul, integral_indicator measurableSet_ball] at hglobal
  have hinitial := integral_mono_of_nonneg (ae_of_all ν hf0) (hw.const_mul C₀)
    (ae_of_all ν (hsmooth μ hμ hχ))
  rw [integral_const_mul, hswap] at hinitial
  have hw_eq : (∫ u : V, ∫ v : V, f u * polynomialKernel (p+1) (v-u) ∂ν) =
      ∫ u : V, f u * W u := by
    congr 1
    ext u
    exact integral_const_mul _ _
  rw [hw_eq] at hinitial
  have hbound := hinitial.trans (mul_le_mul_of_nonneg_left hglobal hC₀.le)
  have hball0 : 0 ≤ ∫ u : V in Metric.ball 0 (4*B), f u :=
    integral_nonneg hf0
  change (∫ v : V, f v ∂ν) ≤
    C₀ * (1+J+T) * (A * ∫ u : V in Metric.ball 0 (4*B), f u) + C₀ * (1+J+T)
  dsimp only [T] at *
  nlinarith [mul_nonneg hA hball0, mul_nonneg hJ (mul_nonneg hA hball0),
    mul_nonneg hT (mul_nonneg hA hball0)]

end PolynomialFourierSmoothing
end CurrentFalconer
end CriticalFourierSupport
end
end

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section AnnularGeometry
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [NormedSpace ℝ V] [BorelSpace V] in

theorem sphere_cap_ball_bound (ξ : Measure V) {δ S L r : ℝ}
    (hS : 0 ≤ S) (hL : 1 ≤ L) (hr : 0 < r) (hδ : δ ≤ r)
    (hmass : ξ Set.univ ≤ 1) (hsphere : ∀ᵐ w ∂ξ, ‖w‖ = 1)
    (hcap : ∀ w : V, ‖w‖ = 1 → ∀ u : ℝ, δ ≤ u → u ≤ 1 →
      ξ (Metric.ball w u) ≤ ENNReal.ofReal (L * u^S)) (x : V) :
    ξ (Metric.ball x r) ≤ ENNReal.ofReal (L * (2*r)^S) := by
  by_cases hlarge : 1 ≤ 2*r
  · apply (measure_mono (Set.subset_univ _)).trans (hmass.trans _)
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.one_le_rpow hlarge hS]
  · by_cases hex : ∃ w : V, ‖w‖ = 1 ∧ w ∈ Metric.ball x r
    · obtain ⟨w,hw,hwx⟩ := hex
      apply le_trans _ (hcap w hw (2*r) (by linarith) (by linarith))
      apply measure_mono
      intro z hz
      have hz' : dist z x < r := hz
      have hw' : dist x w < r := by simpa only [Metric.mem_ball, dist_comm] using hwx
      exact lt_of_le_of_lt (dist_triangle z x w) (by linarith)
    · have hz : ξ (Metric.ball x r) ≤ ξ ∅ := by
        apply measure_mono_ae
        filter_upwards [hsphere] with w hw
        intro hwx
        exact (hex ⟨w,hw,hwx⟩).elim
      rw [measure_empty] at hz
      exact hz.trans (by positivity)

def annularScalarSet (B H : ℝ) : Set ℝ :=
  {s | B ≤ |s| ∧ |s| ≤ min (2*B) H}

theorem measurableSet_annularScalarSet (B H : ℝ) :
    MeasurableSet (annularScalarSet B H) :=
  (measurableSet_le measurable_const measurable_id.abs).inter
    (measurableSet_le measurable_id.abs measurable_const)

theorem volume_annularScalarSet_le {B H : ℝ} (hB : 0 ≤ B) :
    volume (annularScalarSet B H) ≤ ENNReal.ofReal (2*B) := by
  have hs : annularScalarSet B H ⊆ Set.Icc (-2*B) (-B) ∪ Set.Icc B (2*B) := by
    intro s hs
    change B ≤ |s| ∧ |s| ≤ min (2*B) H at hs
    have hs2 := hs.2.trans (min_le_left _ _)
    by_cases hsign : 0 ≤ s
    · right
      rw [abs_of_nonneg hsign] at hs hs2
      exact ⟨hs.1, hs2⟩
    · left
      rw [abs_of_neg (lt_of_not_ge hsign)] at hs hs2
      constructor <;> linarith [hs.1]
  apply (measure_mono hs).trans ((measure_union_le _ _).trans _)
  rw [Real.volume_Icc, Real.volume_Icc]
  have he : -B-(-2*B) = B := by ring
  have he' : 2*B-B = B := by ring
  rw [he, he', ← ENNReal.ofReal_add hB hB]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

def radialWindow (a : ℝ) : Set ℝ :=
  Set.Icc (a-1) (a+1) ∪ Set.Icc (-a-1) (-a+1)

theorem measurableSet_radialWindow (a : ℝ) : MeasurableSet (radialWindow a) :=
  measurableSet_Icc.union measurableSet_Icc

theorem volume_radialWindow_le (a : ℝ) :
    volume (radialWindow a) ≤ 4 := by
  apply (measure_union_le _ _).trans
  rw [Real.volume_Icc, Real.volume_Icc]
  norm_num [show a+1-(a-1) = 2 by ring, show -a+1-(-a-1) = 2 by ring]

omit [MeasurableSpace V] [BorelSpace V] in
theorem smul_mem_ball_radialWindow {s : ℝ} {w x : V} (hw : ‖w‖ = 1)
    (hx : s • w ∈ Metric.ball x 1) : s ∈ radialWindow ‖x‖ := by
  have hd := abs_norm_sub_norm_le (s • w) x
  rw [norm_smul, Real.norm_eq_abs, hw, mul_one] at hd
  have hx' : ‖s • w - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have habs : abs (|s| - ‖x‖) < 1 := hd.trans_lt hx'
  have hb := abs_lt.mp habs
  by_cases hsign : 0 ≤ s
  · left
    rw [abs_of_nonneg hsign] at hb
    constructor <;> linarith
  · right
    rw [abs_of_neg (lt_of_not_ge hsign)] at hb
    constructor <;> linarith

omit [MeasurableSpace V] [BorelSpace V] in
theorem smul_mem_ball_of_inv {s B : ℝ} (hB : 0 < B) (hs : B ≤ |s|)
    {w x : V} (hx : s • w ∈ Metric.ball x 1) :
    w ∈ Metric.ball (s⁻¹ • x) B⁻¹ := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs; linarith
  have he : w - s⁻¹ • x = s⁻¹ • (s • w-x) := by
    rw [smul_sub, inv_smul_smul₀ hs0]
  rw [Metric.mem_ball, dist_eq_norm, he, norm_smul, norm_inv, Real.norm_eq_abs]
  have hh : ‖s • w-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hpos : 0 < |s| := lt_of_lt_of_le hB hs
  have hb := inv_le_inv₀ hpos hB |>.mpr hs
  have hi := mul_lt_mul_of_pos_left hh (inv_pos.mpr hpos)
  simpa only [mul_one] using hi.trans_le (by simpa only [mul_one] using hb)

instance finite_annularScalar (B H : ℝ) :
    IsFiniteMeasure (volume.restrict (annularScalarSet B H)) where
  measure_univ_lt_top := by
    rw [Measure.restrict_apply_univ]
    apply lt_of_le_of_lt (measure_mono (show annularScalarSet B H ⊆
        Metric.closedBall (0 : ℝ) |2*B| from ?_)) measure_closedBall_lt_top
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hs.2.trans ((min_le_left _ _).trans (le_abs_self _))

variable [SecondCountableTopology V]

noncomputable def annularFrequencyMeasure (ξ : Measure V) (B H : ℝ) : Measure V :=
  Measure.map (fun z : ℝ × V => z.1 • z.2)
    ((volume.restrict (annularScalarSet B H)).prod ξ)

instance finite_annularFrequencyMeasure (ξ : Measure V) [IsFiniteMeasure ξ] (B H : ℝ) :
    IsFiniteMeasure (annularFrequencyMeasure ξ B H) := by
  unfold annularFrequencyMeasure
  infer_instance

theorem annularFrequencyMeasure_mass (ξ : Measure V) [IsFiniteMeasure ξ]
    {B H : ℝ} (hB : 0 ≤ B) (hmass : ξ Set.univ ≤ 1) :
    annularFrequencyMeasure ξ B H Set.univ ≤ ENNReal.ofReal (2*B) := by
  rw [annularFrequencyMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ]
  exact (mul_le_mul_right hmass _).trans (by
    simpa only [mul_one] using volume_annularScalarSet_le (H := H) hB)

theorem annularFrequencyMeasure_support (ξ : Measure V) [IsFiniteMeasure ξ]
    (hsphere : ∀ᵐ w ∂ξ, ‖w‖ = 1) (B H : ℝ) :
    ∀ᵐ v ∂annularFrequencyMeasure ξ B H, ‖v‖ ≤ 2*B := by
  unfold annularFrequencyMeasure
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [ae_restrict_mem (measurableSet_annularScalarSet B H)] with s hs
  filter_upwards [hsphere] with w hw
  rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
  exact hs.2.trans (min_le_left _ _)

theorem annularFrequencyMeasure_ball (ξ : Measure V) [IsFiniteMeasure ξ]
    {R S L B H : ℝ} (hB : 0 < B) (hBR : B ≤ R) (hS : 0 ≤ S) (hL : 1 ≤ L)
    (hmass : ξ Set.univ ≤ 1) (hsphere : ∀ᵐ w ∂ξ, ‖w‖ = 1)
    (hcap : ∀ w : V, ‖w‖ = 1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ξ (Metric.ball w r) ≤ ENNReal.ofReal (L*r^S)) (x : V) :
    annularFrequencyMeasure ξ B H (Metric.ball x 1) ≤
      ENNReal.ofReal (4 * L * (2*B⁻¹)^S) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (L * (2*B⁻¹)^S)
  have hδ : R⁻¹ ≤ B⁻¹ := (inv_le_inv₀ (hB.trans_le hBR) hB).mpr hBR
  have hslice (s : ℝ) (hs : s ∈ annularScalarSet B H) :
      ξ {w : V | s • w ∈ Metric.ball x 1} ≤
        (radialWindow ‖x‖).indicator (fun _ => C) s := by
    by_cases hw : s ∈ radialWindow ‖x‖
    · rw [Set.indicator_of_mem hw]
      apply le_trans (measure_mono (fun w hw => smul_mem_ball_of_inv hB hs.1 hw))
      exact sphere_cap_ball_bound ξ hS hL (inv_pos.mpr hB) hδ hmass hsphere hcap
        (s⁻¹ • x)
    · rw [Set.indicator_of_notMem hw]
      have hz : ξ {w : V | s • w ∈ Metric.ball x 1} ≤ ξ ∅ := by
        apply measure_mono_ae
        filter_upwards [hsphere] with w hsw
        intro hx
        exact (hw (smul_mem_ball_radialWindow hsw hx)).elim
      simpa only [measure_empty] using hz
  rw [annularFrequencyMeasure, Measure.map_apply (by fun_prop) measurableSet_ball,
    Measure.prod_apply (measurableSet_ball.preimage (by fun_prop))]
  have hi := lintegral_mono_ae (μ := volume.restrict (annularScalarSet B H))
    (show ∀ᵐ s ∂volume.restrict (annularScalarSet B H),
      ξ (Prod.mk s ⁻¹' ((fun z : ℝ × V => z.1 • z.2) ⁻¹' Metric.ball x 1)) ≤
        (radialWindow ‖x‖).indicator (fun _ => C) s from by
          filter_upwards [ae_restrict_mem (measurableSet_annularScalarSet B H)] with s hs
          exact hslice s hs)
  refine hi.trans ?_
  rw [lintegral_indicator (measurableSet_radialWindow _), lintegral_const,
    Measure.restrict_apply_univ]
  have hvol : (volume.restrict (annularScalarSet B H)) (radialWindow ‖x‖) ≤ 4 :=
    (Measure.restrict_apply_le _ _).trans (volume_radialWindow_le _)
  apply (mul_le_mul_right hvol C).trans
  dsimp only [C]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ L * (2*B⁻¹)^S)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

end AnnularGeometry
end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
