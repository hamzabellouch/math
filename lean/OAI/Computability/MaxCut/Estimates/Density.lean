import Mathlib
import OAI.Computability.MaxCut.Games.Identities

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman

open scoped Real Topology NNReal ContDiff
open Set Filter MeasureTheory
open ProbabilityTheory

noncomputable def density (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

noncomputable def cdf (x : ℝ) : ℝ := (1 / 2 : ℝ) + ∫ t in (0 : ℝ)..x, density t

 theorem density_pos (x : ℝ) : 0 < density x := gaussianPDFReal_pos 0 1 x (by norm_num)
 theorem density_nonneg (x : ℝ) : 0 ≤ density x := (density_pos x).le
 theorem density_continuous : Continuous density := by
  unfold density gaussianPDFReal
  fun_prop

 theorem density_integrable : Integrable density := integrable_gaussianPDFReal 0 1

 theorem density_neg (x : ℝ) : density (-x) = density x := by
  simp [density, gaussianPDFReal]

 theorem density_deriv (x : ℝ) : HasDerivAt density (-x * density x) x := by
  unfold density gaussianPDFReal
  convert (HasDerivAt.const_mul (√(2 * Real.pi * (1 : ℝ≥0) : ℝ))⁻¹
    (((hasDerivAt_id x).pow 2).neg.div_const (2 * (1 : ℝ≥0))).exp) using 1 <;>
    norm_num
  all_goals first | rfl | ring

 theorem cdf_deriv (x : ℝ) : HasDerivAt cdf (density x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (density_continuous.intervalIntegrable 0 x)
    density_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    density_continuous.continuousAt
  convert h.const_add (1 / 2 : ℝ) using 1
  rfl

 theorem cdf_continuous : Continuous cdf := continuous_iff_continuousAt.mpr
  (fun x => (cdf_deriv x).continuousAt)

 theorem cdf_strictMono : StrictMono cdf := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(cdf_deriv x).deriv]
  exact density_pos x

@[simp] theorem cdf_zero : cdf 0 = 1 / 2 := by simp [cdf]

 theorem integral_density : ∫ x, density x = 1 :=
  integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)

 theorem half_integral : ∫ x in Iic (0 : ℝ), density x = 1 / 2 := by
  have he : (∫ x in Iic (0 : ℝ), density x) = ∫ x in Ioi (0 : ℝ), density x := by
    simpa only [density_neg, neg_zero] using integral_comp_neg_Iic 0 density
  have h := intervalIntegral.integral_Iic_add_Ioi (b := 0)
    density_integrable.integrableOn density_integrable.integrableOn
  rw [integral_density, ← he] at h
  linarith

 theorem cdf_eq_integral (x : ℝ) : cdf x = ∫ t in Iic x, density t := by
  have h := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x)
    density_integrable.integrableOn density_integrable.integrableOn
  rw [half_integral] at h
  unfold cdf
  linarith

 theorem cdf_mem_Ioo (x : ℝ) : cdf x ∈ Ioo (0 : ℝ) 1 := by
  have h0 (y : ℝ) : 0 ≤ cdf y := by
    rw [cdf_eq_integral]
    exact integral_nonneg density_nonneg
  have h1 (y : ℝ) : cdf y ≤ 1 := by
    rw [cdf_eq_integral]
    have h := intervalIntegral.integral_Iic_add_Ioi (b := y)
      density_integrable.integrableOn density_integrable.integrableOn
    rw [integral_density] at h
    have hn : 0 ≤ ∫ t in Ioi y, density t := integral_nonneg density_nonneg
    linarith
  exact ⟨(h0 (x - 1)).trans_lt (cdf_strictMono (by linarith)),
    (cdf_strictMono (show x < x + 1 by linarith)).trans_le (h1 (x + 1))⟩

 theorem cdf_neg (x : ℝ) : cdf (-x) = 1 - cdf x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) density
  simp only [density_neg, neg_zero] at h
  have h' : (∫ t in (0 : ℝ)..-x, density t) = -(∫ t in (0 : ℝ)..x, density t) := by
    rw [intervalIntegral.integral_symm, ← h]
  dsimp [cdf]
  rw [h']
  ring

 theorem cdf_tendsto_atBot : Tendsto cdf atBot (𝓝 0) := by
  convert (tendsto_integral_Iic_zero (f := density) (μ := volume) tendsto_id) using 1
  funext x
  exact cdf_eq_integral x

 theorem cdf_tendsto_atTop : Tendsto cdf atTop (𝓝 1) := by
  have h := cdf_tendsto_atBot.comp tendsto_neg_atTop_atBot
  have h' := h.const_sub 1
  simpa only [Function.comp_def, cdf_neg, sub_sub_cancel, sub_zero] using h'

 theorem cdf_range : range cdf = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩; exact cdf_mem_Ioo x
  · have h := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
      cdf_continuous.continuousOn cdf_tendsto_atBot cdf_tendsto_atTop
    simpa only [image_univ] using h

noncomputable def quantile : ℝ → ℝ := Function.invFun cdf

@[simp] theorem quantile_cdf (x : ℝ) : quantile (cdf x) = x :=
  Function.leftInverse_invFun cdf_strictMono.injective x

 theorem cdf_quantile {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : cdf (quantile x) = x := by
  obtain ⟨y, rfl⟩ : x ∈ range cdf := cdf_range.symm ▸ hx
  exact congrArg cdf (quantile_cdf y)

 theorem quantile_strictMonoOn : StrictMonoOn quantile (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  apply cdf_strictMono.lt_iff_lt.mp
  rwa [cdf_quantile ha, cdf_quantile hb]

 theorem quantile_image : quantile '' Ioo (0 : ℝ) 1 = univ := by
  apply eq_univ_of_forall
  intro x
  exact ⟨cdf x, cdf_mem_Ioo x, quantile_cdf x⟩

 theorem quantile_continuousAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt quantile x := by
  apply quantile_strictMonoOn.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hx)
  rw [quantile_image]
  exact univ_mem

 theorem quantile_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt quantile (density (quantile x))⁻¹ x := by
  apply HasDerivAt.of_local_left_inverse (quantile_continuousAt hx)
    (cdf_deriv (quantile x)) (ne_of_gt (density_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact cdf_quantile hy

@[simp] theorem quantile_half : quantile (1 / 2) = 0 := by
  simpa only [cdf_zero] using quantile_cdf 0

/-- Differentiation under a finite integral using the actual compact uniform
bound, to be applied to the Plackett integrand below. -/
 theorem integral_hasDerivAt_compact {F F' : ℝ → ℝ → ℝ} {a b u v x : ℝ}
    (hx : x ∈ Ioo u v) (hab : a ≤ b)
    (hc : ContinuousOn (Function.uncurry F) (Icc u v ×ˢ Icc a b))
    (hc' : ContinuousOn (Function.uncurry F') (Icc u v ×ˢ Icc a b))
    (hd : ∀ z ∈ Icc u v, ∀ t ∈ Icc a b, HasDerivAt (F · t) (F' z t) z) :
    HasDerivAt (fun z => ∫ t in a..b, F z t) (∫ t in a..b, F' x t) x := by
  have section_cont {H : ℝ → ℝ → ℝ}
      (hh : ContinuousOn (Function.uncurry H) (Icc u v ×ˢ Icc a b))
      {z : ℝ} (hz : z ∈ Icc u v) : ContinuousOn (H z) (Icc a b) := by
    exact hh.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hz, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc'
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a b)) (F := F) (F' := F') (bound := fun _ => C)
    (Icc_mem_nhds hx.1 hx.2)
    (show ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) (volume.restrict (Ioc a b)) from by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with z hz
      exact ((section_cont hc hz).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (((section_cont hc ⟨hx.1.le, hx.2.le⟩).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (((section_cont hc' ⟨hx.1.le, hx.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc)
    (show ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ z ∈ Icc u v, ‖F' z t‖ ≤ C from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht z hz
      exact hC (z, t) ⟨hz, Ioc_subset_Icc_self ht⟩)
    (integrable_const C)
    (show ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ z ∈ Icc u v,
      HasDerivAt (F · t) (F' z t) z from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht z hz
      exact hd z hz t (Ioc_subset_Icc_self ht))
  simpa only [intervalIntegral.integral_of_le hab] using h.2

noncomputable def sigma (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
noncomputable def conditionalArg (t u v : ℝ) : ℝ := (v - t * u) / sigma t
noncomputable def plackett (t u v : ℝ) : ℝ :=
  density u * density (conditionalArg t u v) / sigma t
noncomputable def kernel (t x y : ℝ) : ℝ :=
  x * y + ∫ r in (0 : ℝ)..t, plackett r (quantile x) (quantile y)

 theorem sigma_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < sigma t := by
  apply Real.sqrt_pos.mpr
  nlinarith [ht.1, ht.2]

 theorem sigma_sq {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : (sigma t) ^ 2 = 1 - t ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [ht.1, ht.2]

 theorem sigma_continuous : Continuous sigma := by unfold sigma; fun_prop

 theorem sigma_deriv {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt sigma (-t / sigma t) t := by
  have h := ((hasDerivAt_id t).pow 2).const_sub 1
  convert h.sqrt (ne_of_gt (show 0 < 1 - t ^ 2 by nlinarith [ht.1, ht.2])) using 1 <;>
    first | rfl | (dsimp [sigma]; ring)

 theorem plackett_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    0 < plackett t u v := div_pos (mul_pos (density_pos _) (density_pos _)) (sigma_pos ht)

 theorem conditionalArg_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => conditionalArg p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold conditionalArg
  exact ((continuous_snd.snd.sub (continuous_fst.mul continuous_snd.fst)).continuousOn).div
    (sigma_continuous.comp continuous_fst).continuousOn (fun p hp => ne_of_gt (sigma_pos hp))

 theorem plackett_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => plackett p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold plackett
  exact ((density_continuous.comp continuous_snd.fst).continuousOn.mul
    (density_continuous.comp_continuousOn conditionalArg_continuousOn)).div
    (sigma_continuous.comp continuous_fst).continuousOn (fun p hp => ne_of_gt (sigma_pos hp))

 theorem kernel_ge_product {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y : ℝ) :
    x * y ≤ kernel t x y := by
  have h : 0 ≤ ∫ r in (0 : ℝ)..t, plackett r (quantile x) (quantile y) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro r hr
    exact (plackett_pos ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩ _ _).le
  exact le_add_of_nonneg_right h

 theorem density_mul (u v : ℝ) : density u * density v =
    density 0 ^ 2 * Real.exp (-u ^ 2 / 2 + -v ^ 2 / 2) := by
  simp only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero, Real.exp_add]
  ring

 theorem density_zero_sq : density 0 ^ 2 = (2 * Real.pi)⁻¹ := by
  have h : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  simp only [density, gaussianPDFReal, NNReal.coe_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one, inv_pow, h]

 theorem plackett_symm {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    plackett t u v = plackett t v u := by
  have hn := ne_of_gt (sigma_pos ht)
  have he : -u ^ 2 / 2 + -(conditionalArg t u v) ^ 2 / 2 =
      -v ^ 2 / 2 + -(conditionalArg t v u) ^ 2 / 2 := by
    unfold conditionalArg
    calc
      _ = -(u ^ 2 * sigma t ^ 2 + (v - t * u) ^ 2) / (2 * sigma t ^ 2) := by
        field_simp; ring
      _ = -(v ^ 2 * sigma t ^ 2 + (u - t * v) ^ 2) / (2 * sigma t ^ 2) := by
        rw [sigma_sq ht]; ring
      _ = _ := by field_simp; ring
  unfold plackett
  rw [density_mul, density_mul, he]

 theorem kernel_symm {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y : ℝ) :
    kernel t x y = kernel t y x := by
  unfold kernel
  rw [mul_comm x y]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact plackett_symm ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩ _ _

 theorem kernel_half {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    kernel t (1 / 2) (1 / 2) = 1 / 4 + Real.arcsin t / (2 * Real.pi) := by
  have hi : IntervalIntegrable (fun r => 1 / sigma r) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div sigma_continuous.continuousOn (fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      exact ne_of_gt (sigma_pos ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := Real.arcsin) (f' := fun r => 1 / sigma r)
    (fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      exact Real.hasDerivAt_arcsin (by linarith [hr.1]) (ne_of_lt (hr.2.trans_lt ht.2))) hi
  simp only [kernel, quantile_half, plackett, conditionalArg, mul_zero, sub_zero, zero_div,
    ← pow_two, density_zero_sq]
  simp only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul] at h ⊢
  rw [h, Real.arcsin_zero, sub_zero]
  ring

 theorem conditionalArg_deriv_u (t u v : ℝ) :
    HasDerivAt (fun z => conditionalArg t z v) (-t / sigma t) u := by
  convert (((hasDerivAt_id u).const_mul t).const_sub v).div_const (sigma t) using 1 <;>
    first | rfl | simp

 theorem conditionalArg_deriv_v (t u v : ℝ) :
    HasDerivAt (conditionalArg t u) (1 / sigma t) v := by
  convert ((hasDerivAt_id v).sub_const (t * u)).div_const (sigma t) using 1
  rfl

 theorem conditionalArg_deriv_t {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun r => conditionalArg r u v) ((t * v - u) / sigma t ^ 3) t := by
  have hn := ne_of_gt (sigma_pos ht)
  have he : ((-u) * sigma t - (v - t * u) * (-t / sigma t)) / sigma t ^ 2 =
      (t * v - u) / sigma t ^ 3 := by
    field_simp
    rw [sigma_sq ht]
    ring
  convert (((hasDerivAt_id t).mul_const u).const_sub v).div (sigma_deriv ht) hn using 1 <;> try rfl
  simpa only [id_eq, one_mul] using he.symm

 theorem plackett_deriv_u {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun z => plackett t z v)
      (density u * density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3) u := by
  have hn := ne_of_gt (sigma_pos ht)
  have hd := ((density_deriv u).mul
    ((density_deriv (conditionalArg t u v)).comp u (conditionalArg_deriv_u t u v))).div_const
      (sigma t)
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_apply]
  unfold conditionalArg
  field_simp
  rw [sigma_sq ht]
  ring

 theorem plackett_quantile_deriv_x {t x : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (y : ℝ) :
    HasDerivAt (fun z => plackett t (quantile z) (quantile y))
      (density (conditionalArg t (quantile x) (quantile y)) *
        (t * quantile y - quantile x) / sigma t ^ 3) x := by
  convert (plackett_deriv_u ht (quantile x) (quantile y)).comp x (quantile_deriv hx) using 1 <;> try rfl
  field_simp [ne_of_gt (density_pos (quantile x))]

 theorem conditionalCDF_deriv_t {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun r => cdf (conditionalArg r u v))
      (density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3) t := by
  convert (cdf_deriv (conditionalArg t u v)).comp t (conditionalArg_deriv_t ht u v) using 1 <;> try rfl
  ring

noncomputable def flux (t u v : ℝ) : ℝ :=
  density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3

 theorem flux_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => flux p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold flux
  exact ((density_continuous.comp_continuousOn conditionalArg_continuousOn).mul
    ((continuous_fst.mul continuous_snd.snd).sub continuous_snd.fst).continuousOn).div
    ((sigma_continuous.comp continuous_fst).pow 3).continuousOn
    (fun p hp => pow_ne_zero _ (ne_of_gt (sigma_pos hp)))

 theorem quantile_continuousOn : ContinuousOn quantile (Ioo (0 : ℝ) 1) :=
  fun _ hx => (quantile_continuousAt hx).continuousWithinAt

 theorem kernel_deriv_x {t x y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => kernel t z y) (cdf (conditionalArg t (quantile x) (quantile y))) x := by
  let u := x / 2
  let v := (x + 1) / 2
  have huxv : x ∈ Ioo u v := by dsimp [u, v]; constructor <;> linarith [hx.1, hx.2]
  have huv : Icc u v ⊆ Ioo (0 : ℝ) 1 := by
    intro z hz; dsimp [u, v] at hz; constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
  have hrt : Icc (0 : ℝ) t ⊆ Ioo (-1 : ℝ) 1 := by
    intro r hr; exact ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩
  have hm : ContinuousOn (fun p : ℝ × ℝ => (p.2, quantile p.1, quantile y))
      (Icc u v ×ˢ Icc (0 : ℝ) t) := by
    apply continuous_snd.continuousOn.prodMk
    exact (quantile_continuousOn.comp continuous_fst.continuousOn
      (fun p hp => huv hp.1)).prodMk continuousOn_const
  have hc := plackett_continuousOn.comp hm (fun p hp => hrt hp.2)
  have hc' := flux_continuousOn.comp hm (fun p hp => hrt hp.2)
  have hd := integral_hasDerivAt_compact (F := fun z r => plackett r (quantile z) (quantile y))
    (F' := fun z r => flux r (quantile z) (quantile y)) huxv ht.1 hc hc'
    (fun z hz r hr => plackett_quantile_deriv_x (hrt hr) (huv hz) y)
  have hint : (∫ r in (0 : ℝ)..t, flux r (quantile x) (quantile y)) =
      cdf (conditionalArg t (quantile x) (quantile y)) - y := by
    have hfc : ContinuousOn (fun r => flux r (quantile x) (quantile y)) (uIcc 0 t) := by
      apply flux_continuousOn.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const)).continuousOn
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      exact hrt hr
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun r hr => conditionalCDF_deriv_t (hrt (by rwa [uIcc_of_le ht.1] at hr))
        (quantile x) (quantile y)) hfc.intervalIntegrable
    simpa only [flux, conditionalArg, sigma, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      Real.sqrt_one, zero_mul, div_one, cdf_quantile hy] using hh
  convert ((hasDerivAt_id x).mul_const y).add hd using 1 <;> try rfl
  simp only [one_mul]
  rw [hint]
  ring

 theorem kernel_deriv_y {t x y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (kernel t x) (cdf (conditionalArg t (quantile y) (quantile x))) y := by
  have h := kernel_deriv_x ht hy hx
  have he : (fun z => kernel t z x) = kernel t x := by
    funext z; exact kernel_symm ht z x
  rwa [he] at h

noncomputable def kernelX (t x y : ℝ) : ℝ := cdf (conditionalArg t (quantile x) (quantile y))
noncomputable def kernelXX (t x y : ℝ) : ℝ :=
  -t * plackett t (quantile x) (quantile y) / density (quantile x) ^ 2
noncomputable def kernelXY (t x y : ℝ) : ℝ :=
  plackett t (quantile x) (quantile y) / (density (quantile x) * density (quantile y))

 theorem kernelX_deriv_x {t x y : ℝ} (_ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => kernelX t z y) (kernelXX t x y) x := by
  have h := (cdf_deriv (conditionalArg t (quantile x) (quantile y))).comp x
    ((conditionalArg_deriv_u t (quantile x) (quantile y)).comp x (quantile_deriv hx))
  convert h using 1 <;> try rfl
  unfold kernelXX plackett
  field_simp [ne_of_gt (density_pos (quantile x))]

 theorem kernelX_deriv_y {t x y : ℝ} (_ht : t ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (kernelX t x) (kernelXY t x y) y := by
  have h := (cdf_deriv (conditionalArg t (quantile x) (quantile y))).comp y
    ((conditionalArg_deriv_v t (quantile x) (quantile y)).comp y (quantile_deriv hy))
  convert h using 1 <;> try rfl
  unfold kernelXY plackett
  field_simp [ne_of_gt (density_pos (quantile x)), ne_of_gt (density_pos (quantile y))]

 theorem kernel_weighted_hessian {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y a b : ℝ) :
    kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 =
      -t * plackett t (quantile x) (quantile y) *
        (a / density (quantile x) - b / density (quantile y)) ^ 2 := by
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  unfold kernelXX kernelXY
  rw [plackett_symm ht' (quantile y) (quantile x)]
  field_simp [ne_of_gt (density_pos (quantile x)), ne_of_gt (density_pos (quantile y))]
  ring

 theorem kernel_weighted_hessian_nonpos {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y a b : ℝ) :
    kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 ≤ 0 := by
  rw [kernel_weighted_hessian ht]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.1])
      (plackett_pos ⟨by linarith [ht.1], ht.2⟩ _ _).le
  · exact sq_nonneg _

 theorem density_contDiff (n : ℕ∞ω) : ContDiff ℝ n density := by
  unfold density gaussianPDFReal
  fun_prop

 theorem cdf_contDiff (n : ℕ) : ContDiff ℝ n cdf := by
  cases n with
  | zero => exact contDiff_zero.mpr cdf_continuous
  | succ n =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun x => (cdf_deriv x).differentiableAt, by simp, ?_⟩
    have he : deriv cdf = density := funext (fun x => (cdf_deriv x).deriv)
    rw [he]
    exact density_contDiff n

 theorem quantile_contDiffOn (n : ℕ) : ContDiffOn ℝ n quantile (Ioo (0 : ℝ) 1) := by
  induction n with
  | zero => exact contDiffOn_zero.mpr quantile_continuousOn
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (quantile_deriv hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h : ContDiffOn ℝ n (fun x => (density (quantile x))⁻¹) (Ioo (0 : ℝ) 1) := by
      exact ((density_contDiff n).comp_contDiffOn ih).inv (fun _ _ => ne_of_gt (density_pos _))
    apply h.congr
    intro x hx
    exact (quantile_deriv hx).deriv

 theorem kernelX_contDiffOn {t : ℝ} (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (kernelX t)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hx : ContDiffOn ℝ n (fun p : ℝ × ℝ => quantile p.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (quantile_contDiffOn n).comp contDiffOn_fst (fun _ hp => hp.1)
  have hy : ContDiffOn ℝ n (fun p : ℝ × ℝ => quantile p.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (quantile_contDiffOn n).comp contDiffOn_snd (fun _ hp => hp.2)
  exact (cdf_contDiff n).comp_contDiffOn ((hy.sub (contDiffOn_const.mul hx)).div_const (sigma t))

noncomputable def kernelD (t : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  kernelX t p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
  kernelX t p.2 p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ

 theorem kernelD_contDiffOn (t : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (kernelD t) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hswap : ContDiffOn ℝ n (fun p : ℝ × ℝ => kernelX t p.2 p.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (kernelX_contDiffOn n).comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)
  exact ((kernelX_contDiffOn n).smul_const _).add (hswap.smul_const _)

 theorem kernel_fderiv {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    HasFDerivAt (Function.uncurry (kernel t)) (kernelD t p) p := by
  have hn := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp
  have hc : ContinuousAt (Function.uncurry (kernelX t)) p :=
    (kernelX_contDiffOn 0).continuousOn.continuousAt hn
  have hswap : ContDiffOn ℝ 0 (fun q : ℝ × ℝ => kernelX t q.2 q.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (kernelX_contDiffOn 0).comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hq => ⟨hq.2, hq.1⟩)
  have hcs : ContinuousAt (fun q : ℝ × ℝ => kernelX t q.2 q.1) p :=
    hswap.continuousOn.continuousAt hn
  have hf := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := kernel t)
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (kernelX t x y))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (kernelX t y x))
    (Filter.mem_of_superset hn (fun q hq => (kernel_deriv_x ht hq.1 hq.2).hasFDerivAt))
    (Filter.mem_of_superset hn (fun q hq => (kernel_deriv_y ht hq.1 hq.2).hasFDerivAt))
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hcs)
  convert hf.hasFDerivAt using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro q
  change kernelX t p.1 p.2 * q.1 + kernelX t p.2 p.1 * q.2 =
    q.1 * kernelX t p.1 p.2 + q.2 * kernelX t p.2 p.1
  ring

 theorem kernel_contDiffOn {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (kernel t)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  cases n with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (kernel_fderiv ht hp).continuousAt.continuousWithinAt
  | succ n =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_Ioo)]
    refine ⟨fun p hp => (kernel_fderiv ht hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply (kernelD_contDiffOn t n).congr
    intro p hp
    exact (kernel_fderiv ht hp).fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem affinePath_deriv (p d : E) (u : ℝ) :
    HasDerivAt (fun v : ℝ => p + v • d) d u := by
  simpa using ((hasDerivAt_id u).smul_const d).const_add p

 theorem affinePath_iterated_two (p d : E) (u : ℝ) :
    iteratedDeriv 2 (fun v : ℝ => p + v • d) u = 0 := by
  rw [iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_smul_const (f := fun v : ℝ => v) (contDiffAt_id : ContDiffAt ℝ 2 _ _)]
  simp [iteratedDeriv_fun_id]

 theorem affinePath_iterated_three (p d : E) (u : ℝ) :
    iteratedDeriv 3 (fun v : ℝ => p + v • d) u = 0 := by
  rw [iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_smul_const (f := fun v : ℝ => v) (contDiffAt_id : ContDiffAt ℝ 3 _ _)]
  simp [iteratedDeriv_fun_id]

 theorem iteratedDeriv_affinePath_two {F : E → ℝ} {p d : E} {u : ℝ}
    (hf : ContDiffAt ℝ 2 F (p + u • d)) :
    iteratedDeriv 2 (fun v : ℝ => F (p + v • d)) u =
      iteratedFDeriv ℝ 2 F (p + u • d) (fun _ => d) := by
  have h := iteratedDeriv_vcomp_two hf
    (show ContDiffAt ℝ 2 (fun v : ℝ => p + v • d) u by fun_prop)
  simpa [Function.comp_def, (affinePath_deriv p d u).deriv,
    affinePath_iterated_two] using h

 theorem iteratedDeriv_affinePath_three {F : E → ℝ} {p d : E} {u : ℝ}
    (hf : ContDiffAt ℝ 3 F (p + u • d)) :
    iteratedDeriv 3 (fun v : ℝ => F (p + v • d)) u =
      iteratedFDeriv ℝ 3 F (p + u • d) (fun _ => d) := by
  have h := iteratedDeriv_vcomp_three hf
    (show ContDiffAt ℝ 3 (fun v : ℝ => p + v • d) u by fun_prop)
  have hz₀ := (iteratedFDeriv ℝ 2 F (p + u • d)).map_coord_zero
    (m := ![0, d]) 0 (by simp)
  have hz₁ := (iteratedFDeriv ℝ 2 F (p + u • d)).map_coord_zero
    (m := ![d, 0]) 1 (by simp)
  simpa [Function.comp_def, (affinePath_deriv p d u).deriv,
    affinePath_iterated_two, affinePath_iterated_three, hz₀, hz₁] using h

 theorem compact_third_derivative_bound {O K : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {F : E → ℝ} (hf : ContDiffOn ℝ 3 F O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖iteratedFDeriv ℝ 3 F p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ 3 F) O := by
    apply (hf.continuousOn_iteratedFDerivWithin (by norm_num) hO.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      (hf.contDiffAt (hO.mem_nhds hp)) hp).symm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKO)
  refine ⟨max 0 C, le_max_left _ _, fun p hp => (hC p hp).trans (le_max_right _ _)⟩

 theorem compact_cubic_taylor_bound {O K : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hcv : Convex ℝ K) (hKO : K ⊆ O)
    {F : E → ℝ} (hf : ContDiffOn ℝ 3 F O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ q ∈ K,
      |F q - F p - fderiv ℝ F p (q - p) -
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => q - p)| ≤ C * ‖q - p‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := compact_third_derivative_bound hO hK hKO hf
  refine ⟨C, hC0, ?_⟩
  intro p hp q hq
  let d := q - p
  let g : ℝ → ℝ := fun u => F (p + u • d)
  have hpath (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : p + u • d ∈ K :=
    hcv.add_smul_sub_mem hp hq hu
  have hF (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 F (p + u • d) :=
    hf.contDiffAt (hO.mem_nhds (hKO (hpath u hu)))
  have hg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 g u :=
    (hF u hu).comp u (by fun_prop)
  have hthird (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin 3 g (Icc 0 1) u‖ ≤ C * ‖d‖ ^ 3 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) (hg u hu) hu]
    change ‖iteratedDeriv 3 (fun v => F (p + v • d)) u‖ ≤ _
    rw [iteratedDeriv_affinePath_three (hF u hu)]
    simpa using (iteratedFDeriv ℝ 3 F (p + u • d)).le_of_opNorm_le
      (hC _ (hpath u hu)) (fun _ => d)
  have hb := taylor_mean_remainder_bound (n := 2) (a := (0 : ℝ)) (b := 1)
    (x := 1) (by norm_num) (fun u hu => (hg u hu).contDiffWithinAt)
    (by constructor <;> norm_num) hthird
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hg0 : ContDiffAt ℝ 3 g 0 := hg 0 h0
  have hg1 : deriv g 0 = fderiv ℝ F p d := by
    have hh := (hf.contDiffAt (hO.mem_nhds (hKO hp))).differentiableAt (by norm_num)
    have hh' : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • d) := by simpa using hh.hasFDerivAt
    simpa [g, Function.comp_def] using (hh'.comp_hasDerivAt 0 (affinePath_deriv p d 0)).deriv
  have hg2 : iteratedDeriv 2 g 0 = iteratedFDeriv ℝ 2 F p (fun _ => d) := by
    simpa [g] using iteratedDeriv_affinePath_two ((hF 0 h0).of_le (by norm_num))
  have ht : taylorWithinEval g 2 (Icc 0 1) 0 1 =
      F p + fderiv ℝ F p d + (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => d) := by
    rw [taylorWithinEval_succ g 1, taylorWithinEval_succ g 0, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (hg0.of_le (by norm_num)) h0,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (hg0.of_le (by norm_num)) h0]
    simp only [hg2]
    norm_num [g]
    exact hg1
  rw [ht] at hb
  have hg_end : g 1 = F q := by simp [g, d]
  rw [hg_end] at hb
  norm_num at hb
  calc
    _ = |F q - (F p + fderiv ℝ F p d +
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => d))| := by congr 1; dsimp [d]; ring
    _ ≤ C * ‖d‖ ^ 3 / 2 := hb
    _ ≤ C * ‖q - p‖ ^ 3 := div_le_self (by positivity) (by norm_num)

 theorem kernelX_line_deriv {t x y a b u : ℝ} (_ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x + u * a ∈ Ioo (0 : ℝ) 1) (hy : y + u * b ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v : ℝ => kernelX t (x + v * a) (y + v * b))
      (kernelXX t (x + u * a) (y + u * b) * a +
        kernelXY t (x + u * a) (y + u * b) * b) u := by
  have hqx := (quantile_deriv hx).comp u (((hasDerivAt_id u).mul_const a).const_add x)
  have hqy := (quantile_deriv hy).comp u (((hasDerivAt_id u).mul_const b).const_add y)
  have h := (cdf_deriv (conditionalArg t (quantile (x + u * a)) (quantile (y + u * b)))).comp u
    ((hqy.sub (hqx.const_mul t)).div_const (sigma t))
  convert h using 1 <;> try rfl
  unfold kernelXX kernelXY plackett
  field_simp [ne_of_gt (density_pos (quantile (x + u * a))),
    ne_of_gt (density_pos (quantile (y + u * b)))]
  ring

 theorem kernel_line_deriv {t x y a b u : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x + u * a ∈ Ioo (0 : ℝ) 1) (hy : y + u * b ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v : ℝ => kernel t (x + v * a) (y + v * b))
      (kernelX t (x + u * a) (y + u * b) * a +
        kernelX t (y + u * b) (x + u * a) * b) u := by
  have hline : HasDerivAt (fun v : ℝ => (x + v * a, y + v * b)) (a, b) u :=
    by simpa using ((((hasDerivAt_id u).mul_const a).const_add x).prodMk
      (((hasDerivAt_id u).mul_const b).const_add y))
  simpa [Function.comp_def, kernelD] using (kernel_fderiv ht ⟨hx, hy⟩).comp_hasDerivAt u hline

 theorem kernel_line_second {t x y a b : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 2 (fun v : ℝ => kernel t (x + v * a) (y + v * b)) 0 =
      kernelXX t x y * a ^ 2 + 2 * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 := by
  have hx' : x + (0 : ℝ) * a ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  have hy' : y + (0 : ℝ) * b ∈ Ioo (0 : ℝ) 1 := by simpa using hy
  have hne : ∀ᶠ v : ℝ in 𝓝 0, x + v * a ∈ Ioo (0 : ℝ) 1 ∧
      y + v * b ∈ Ioo (0 : ℝ) 1 := by
    have hc : ContinuousAt (fun v : ℝ => (x + v * a, y + v * b)) 0 := by fun_prop
    exact hc.preimage_mem_nhds ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hx', hy'⟩)
  have he : deriv (fun v : ℝ => kernel t (x + v * a) (y + v * b)) =ᶠ[𝓝 0]
      (fun v => kernelX t (x + v * a) (y + v * b) * a +
        kernelX t (y + v * b) (x + v * a) * b) := by
    filter_upwards [hne] with v hv
    exact (kernel_line_deriv ht hv.1 hv.2).deriv
  have hd := ((kernelX_line_deriv ht hx' hy').mul_const a).add
    ((kernelX_line_deriv ht hy' hx').mul_const b)
  have heq : kernelXY t y x = kernelXY t x y := by
    unfold kernelXY
    rw [plackett_symm ⟨by linarith [ht.1], ht.2⟩ (quantile y) (quantile x), mul_comm]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  have hdd := hd.deriv
  simp only [zero_mul, add_zero, heq] at hdd
  convert hdd using 1
  ring

 theorem kernel_second_diagonal {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (d : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry (kernel t)) p (fun _ => d) =
      kernelXX t p.1 p.2 * d.1 ^ 2 + 2 * kernelXY t p.1 p.2 * d.1 * d.2 +
        kernelXX t p.2 p.1 * d.2 ^ 2 := by
  have hf : ContDiffAt ℝ 2 (Function.uncurry (kernel t)) (p + (0 : ℝ) • d) := by
    simpa using (kernel_contDiffOn ht 2).contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)
  have he := iteratedDeriv_affinePath_two hf
  simp only [zero_smul, add_zero] at he
  rw [← he]
  exact kernel_line_second ht hp.1 hp.2

 theorem norm_pair_cube_le (a b : ℝ) : ‖(a, b)‖ ^ 3 ≤ |a| ^ 3 + |b| ^ 3 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)

 theorem kernel_uniform_cubic {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (_hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc η (1 - η) ×ˢ Icc η (1 - η),
      ∀ q ∈ Icc η (1 - η) ×ˢ Icc η (1 - η),
      |kernel t q.1 q.2 - kernel t p.1 p.2 -
        (kernelX t p.1 p.2 * (q.1 - p.1) + kernelX t p.2 p.1 * (q.2 - p.2)) -
        (1 / 2 : ℝ) * (kernelXX t p.1 p.2 * (q.1 - p.1) ^ 2 +
          2 * kernelXY t p.1 p.2 * (q.1 - p.1) * (q.2 - p.2) +
          kernelXX t p.2 p.1 * (q.2 - p.2) ^ 2)| ≤
      C * (|q.1 - p.1| ^ 3 + |q.2 - p.2| ^ 3) := by
  have hsub : Icc η (1 - η) ×ˢ Icc η (1 - η) ⊆
      Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hη.trans_le hp.1.1, by linarith [hp.1.2]⟩,
      ⟨hη.trans_le hp.2.1, by linarith [hp.2.2]⟩⟩
  obtain ⟨C, hC0, hC⟩ := compact_cubic_taylor_bound (isOpen_Ioo.prod isOpen_Ioo)
    (isCompact_Icc.prod isCompact_Icc) ((convex_Icc η (1 - η)).prod (convex_Icc η (1 - η)))
    hsub (kernel_contDiffOn ht 3)
  refine ⟨C, hC0, ?_⟩
  intro p hp q hq
  have hb := hC p hp q hq
  rw [(kernel_fderiv ht (hsub hp)).fderiv, kernel_second_diagonal ht (hsub hp)] at hb
  change |kernel t q.1 q.2 - kernel t p.1 p.2 -
    (kernelX t p.1 p.2 * (q.1 - p.1) + kernelX t p.2 p.1 * (q.2 - p.2)) -
    (1 / 2 : ℝ) * (kernelXX t p.1 p.2 * (q.1 - p.1) ^ 2 +
      2 * kernelXY t p.1 p.2 * (q.1 - p.1) * (q.2 - p.2) +
      kernelXX t p.2 p.1 * (q.2 - p.2) ^ 2)| ≤ C * ‖q - p‖ ^ 3 at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (norm_pair_cube_le (q.1 - p.1) (q.2 - p.2)) hC0)

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def bitPairWeight (t : ℝ) (a b : Bool) : ℝ := (1 + t * sign a * sign b) / 4

 theorem bitPairWeight_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (a b : Bool) :
    0 ≤ bitPairWeight t a b := by
  cases a <;> cases b <;> simp [bitPairWeight, sign] <;> linarith [ht.1, ht.2]

 theorem bitPairWeight_mass (t : ℝ) : ∑ a : Bool, ∑ b : Bool, bitPairWeight t a b = 1 := by
  simp [bitPairWeight, sign]; ring

 theorem bitPairWeight_marginal (t : ℝ) (a : Bool) : ∑ b : Bool, bitPairWeight t a b = 1 / 2 := by
  cases a <;> simp [bitPairWeight, sign] <;> ring

 theorem bitPairWeight_symm (t : ℝ) (a b : Bool) : bitPairWeight t a b = bitPairWeight t b a := by
  unfold bitPairWeight; ring

 theorem kernel_one_bit {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y a b : ℝ,
      (∀ e : Bool, x + sign e * a ∈ Icc η (1 - η)) →
      (∀ e : Bool, y + sign e * b ∈ Icc η (1 - η)) →
      (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
        kernel t (x + sign e * a) (y + sign f * b)) ≤
      kernel t x y + C * (|a| ^ 3 + |b| ^ 3) := by
  obtain ⟨C, hC0, hC⟩ := kernel_uniform_cubic ht hη hη'
  refine ⟨C, hC0, ?_⟩
  intro x y a b hx hy
  have hxp : x ∈ Icc η (1 - η) := by
    have hx0 := hx false; have hx1 := hx true
    simp [sign] at hx0 hx1
    constructor <;> linarith [hx0.1, hx0.2, hx1.1, hx1.2]
  have hyp : y ∈ Icc η (1 - η) := by
    have hy0 := hy false; have hy1 := hy true
    simp [sign] at hy0 hy1
    constructor <;> linarith [hy0.1, hy0.2, hy1.1, hy1.2]
  let Q : Bool → Bool → ℝ := fun e f => kernel t x y +
    (kernelX t x y * (sign e * a) + kernelX t y x * (sign f * b)) +
    (1 / 2 : ℝ) * (kernelXX t x y * (sign e * a) ^ 2 +
      2 * kernelXY t x y * (sign e * a) * (sign f * b) +
      kernelXX t y x * (sign f * b) ^ 2) + C * (|a| ^ 3 + |b| ^ 3)
  have hpoint (e f : Bool) : kernel t (x + sign e * a) (y + sign f * b) ≤ Q e f := by
    have hb := (hC (x, y) ⟨hxp, hyp⟩ (x + sign e * a, y + sign f * b) ⟨hx e, hy f⟩)
    simp only [add_sub_cancel_left] at hb
    have he : |sign e * a| = |a| := by cases e <;> simp [sign]
    have hf : |sign f * b| = |b| := by cases f <;> simp [sign]
    rw [he, hf] at hb
    have hb' := (abs_le.mp hb).2
    dsimp [Q]
    linarith
  have hsum : (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
      kernel t (x + sign e * a) (y + sign f * b)) ≤
      ∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * Q e f := by
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_left (hpoint e f)
      (bitPairWeight_nonneg ⟨by linarith [ht.1], ht.2.le⟩ e f)
  have halg : (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * Q e f) =
      kernel t x y + (1 / 2 : ℝ) *
        (kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2) +
      C * (|a| ^ 3 + |b| ^ 3) := by
    simp only [Fintype.sum_bool, Q, bitPairWeight, sign, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [halg] at hsum
  linarith [kernel_weighted_hessian_nonpos ht x y a b]

 theorem kernel_lipschitz_x {t x x' y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hx' : x' ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |kernel t x' y - kernel t x y| ≤ |x' - x| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z => kernel t z y) (C := 1)
    (fun z hz => (kernel_deriv_x ht hz hy).differentiableAt)
    (fun z hz => by
      rw [(kernel_deriv_x ht hz hy).deriv, Real.norm_eq_abs,
        abs_of_pos (cdf_mem_Ioo _).1]
      exact (cdf_mem_Ioo _).2.le)
    (convex_Ioo (0 : ℝ) 1) hx hx'
  simpa only [Real.norm_eq_abs, one_mul] using hb

 theorem kernel_lipschitz {t x x' y y' : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hx' : x' ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hy' : y' ∈ Ioo (0 : ℝ) 1) :
    |kernel t x' y' - kernel t x y| ≤ |x' - x| + |y' - y| := by
  have h1 := kernel_lipschitz_x ht hx hx' hy'
  have h2 := kernel_lipschitz_x ht hy hy' hx
  rw [kernel_symm ht y' x, kernel_symm ht y x] at h2
  calc
    _ = |(kernel t x' y' - kernel t x y') + (kernel t x y' - kernel t x y)| := by congr 1; ring
    _ ≤ |kernel t x' y' - kernel t x y'| + |kernel t x y' - kernel t x y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

end OptimalMaxCut.GaussianBellman

end

end OAI
