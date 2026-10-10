import Mathlib
import OAI.Geometry.CubicTorus.Regularity.WeightedPerimeter

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def cubeCenter : Cover := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def cubeBall (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball cubeCenter r

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet (cubeBall r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 1 / 2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeBall r = Metric.ball cubeCenter r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (cubeBall r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

def radialBump : ContDiffBump cubeCenter where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def radialCore (x : Cover) : ℝ := radialBump x * (1 - ‖x - cubeCenter‖ ^ 2)

def radialSquared (x : Cover) : ℝ := 1 - latticePeriodize radialCore x

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCore := by
  exact radialBump.contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport radialCore :=
  radialBump.hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport radialCore ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport (radialBump : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [radialBump.tsupport_eq] at hs
  have hnorm : ‖x - cubeCenter‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans hnorm
  change ‖x i - (1 / 2 : ℝ)‖ ≤ 1 / 3 at hb
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialSquared :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    radialSquared (x + latticeVector n) = radialSquared x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    radialSquared x = 1 - radialBump x * (1 - ‖x - cubeCenter‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - cubeCenter‖ < 1 / 4) :
    radialSquared =ᶠ[𝓝 x] (fun y ↦ ‖y - cubeCenter‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := radialBump.eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball cubeCenter radialBump.rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    radialSquared x < t ↔ ‖x - cubeCenter‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - cubeCenter)
  have hb0 : 0 ≤ radialBump x := radialBump.nonneg
  have hb1 : radialBump x ≤ 1 := radialBump.le_one
  have he (h : ‖x - cubeCenter‖ ^ 2 < 1 / 16) : radialBump x = 1 := by
    apply radialBump.one_of_mem_closedBall
    change dist x cubeCenter ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - cubeCenter‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - cubeCenter‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion radialSquared (r ^ 2) = cubeBall r := by
  ext z
  change radialSquared (representative z) < r ^ 2 ↔
    dist (representative z) cubeCenter < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma norm_gradient_radialSquared_of_mem_cube {x : Cover} (hx : x ∈ fundamentalCube)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (hxt : radialSquared x < r ^ 2) :
    ‖gradient radialSquared x‖ ≤ 2 * r := by
  have hnormsq := (radialSquared_sublevel_iff hx (by nlinarith)).1 hxt
  have hnorm : ‖x - cubeCenter‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr).mp hnormsq
  rw [norm_gradient_eq_norm_fderiv,
    (radialSquared_eventuallyEq_norm_sq (hnorm.trans_le hsmall)).fderiv_eq]
  have he : (fun y : Cover ↦ ‖y - cubeCenter‖ ^ 2) =
      (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) := by simp only [sub_eq_add_neg]
  rw [he]
  have hf : fderiv ℝ (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) x =
      fderiv ℝ (fun y : Cover ↦ ‖y‖ ^ 2) (x + -cubeCenter) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Cover ↦ ‖y‖ ^ 2) (x := x) (-cubeCenter) using 1
  rw [hf, fderiv_norm_sq_apply, two_smul]
  calc
    _ ≤ ‖innerSL ℝ (x + -cubeCenter)‖ + ‖innerSL ℝ (x + -cubeCenter)‖ := norm_add_le _ _
    _ = 2 * ‖x - cubeCenter‖ := by rw [innerSL_apply_norm]; simp only [sub_eq_add_neg]; ring
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm.le (by norm_num)

lemma norm_gradient_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (x : Cover)
    (hxt : radialSquared x < r ^ 2) : ‖gradient radialSquared x‖ ≤ 2 * r := by
  have he := periodic_representative radialSquared_periodic x
  have hg := periodic_representative (f := gradient radialSquared)
    (fun n y ↦ gradient_periodic radialSquared_periodic n y) x
  rw [← hg]
  exact norm_gradient_radialSquared_of_mem_cube (representative_mem_fundamentalCube _) hr hsmall (by rwa [he])

end CubicTorus

namespace CubicTorus

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma centeredBall_eq_cubeBall_preimage (r : ℝ) :
    Metric.ball (0 : Torus) r =
      (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeBall r := by
  rw [cubeBall_eq_metricBall]
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

lemma volume_centeredBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball (0 : Torus) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [centeredBall_eq_cubeBall_preimage,
    volume_translation (measurableSet_cubeBall r).nullMeasurableSet, volume_cubeBall hr0 hr1]

lemma volume_torusBall (a : Torus) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball a r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  have he : Metric.ball a r = (fun z : Torus ↦ z + -a) ⁻¹' Metric.ball 0 r := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero]
  rw [he, volume_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet, volume_centeredBall hr0 hr1]

def localRadialSquared (a : Torus) (x : Cover) : ℝ :=
  radialSquared (x + representative (quotientMap cubeCenter - a))

lemma localRadialSquared_contDiff (a : Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (localRadialSquared a) :=
  radialSquared_contDiff.comp (contDiff_id.add contDiff_const)

lemma localRadialSquared_periodic (a : Torus) (n : Fin 3 → ℤ) (x : Cover) :
    localRadialSquared a (x + latticeVector n) = localRadialSquared a x := by
  unfold localRadialSquared
  rw [show x + latticeVector n + representative (quotientMap cubeCenter - a) =
    (x + representative (quotientMap cubeCenter - a)) + latticeVector n by abel]
  exact radialSquared_periodic n _

lemma sublevelRegion_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4) :
    sublevelRegion (localRadialSquared a) (r ^ 2) = Metric.ball a r := by
  ext z
  have hrep := periodic_representative radialSquared_periodic
    (representative z + representative (quotientMap cubeCenter - a))
  rw [quotientMap_add, quotientMap_representative, quotientMap_representative] at hrep
  change radialSquared (representative z + representative (quotientMap cubeCenter - a)) < r ^ 2 ↔ _
  rw [← hrep]
  change z + (quotientMap cubeCenter - a) ∈ sublevelRegion radialSquared (r ^ 2) ↔ _
  rw [sublevelRegion_radialSquared hr hs, cubeBall_eq_metricBall]
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z + (quotientMap cubeCenter - a) - quotientMap cubeCenter = z - a by abel]

lemma norm_gradient_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4)
    (x : Cover) (hx : localRadialSquared a x < r ^ 2) :
    ‖gradient (localRadialSquared a) x‖ ≤ 2 * r := by
  rw [norm_gradient_eq_norm_fderiv]
  have he : fderiv ℝ (localRadialSquared a) x =
      fderiv ℝ radialSquared (x + representative (quotientMap cubeCenter - a)) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := radialSquared) (x := x)
      (representative (quotientMap cubeCenter - a)) using 1
  rw [he, ← norm_gradient_eq_norm_fderiv]
  exact norm_gradient_radialSquared hr hs _ hx

lemma sublevelVolume_localRadialSquared_le (E : Set Torus) (a : Torus) {r t : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1 / 4) (ht : t ≤ r ^ 2) :
    sublevelVolume E (localRadialSquared a) t ≤ (2 * r) ^ 3 := by
  calc
    _ ≤ sublevelVolume E (localRadialSquared a) (r ^ 2) := sublevelVolume_mono E _ ht
    _ ≤ torusVolume.real (Metric.ball a r) := by
      unfold sublevelVolume
      rw [sublevelRegion_localRadialSquared a hr hs]
      exact measureReal_mono inter_subset_right
    _ = r ^ 3 * (Real.pi * 4 / 3) := by
      rw [Measure.real_def, volume_torusBall a hr (by linarith), ENNReal.toReal_ofReal (by positivity)]
    _ ≤ (2 * r) ^ 3 := by nlinarith [Real.pi_lt_four, pow_nonneg hr 3]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CubicTorus

theorem monotone_density_root_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    T / (6 * c) ≤ m T ^ (1 / 3 : ℝ) := by
  let g : ℝ → ℝ := fun x ↦ m x ^ (1 / 3 : ℝ)
  have hg : Monotone g := fun x y hxy ↦ Real.rpow_le_rpow (hm0 x) (hm hxy) (by norm_num)
  have hderiv : ∀ᵐ x : ℝ, x ∈ Ioo 0 T → 1 / (6 * c) ≤ deriv g x := by
    filter_upwards [hm.ae_differentiableAt, hode] with x hmx hode
    intro hx
    have hmx0 : 0 < m x := hpos x ⟨hx.1, hx.2.le⟩
    have hp : 0 < m x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hmx0 _
    have hgderiv : HasDerivAt g ((1 / 3 : ℝ) * m x ^ (-2 / 3 : ℝ) * deriv m x) x := by
      convert! (Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hmx0.ne')).comp x hmx.hasDerivAt using 1
      norm_num [g, Function.comp_def]
    have hpower : m x ^ (1 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = m x := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have hpower' : m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have he : deriv g x * m x ^ (2 / 3 : ℝ) = deriv m x / 3 := by
      rw [hgderiv.deriv]
      calc
        _ = (m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ)) * deriv m x / 3 := by ring
        _ = _ := by rw [hpower']; ring
    have hbr : b * m x ^ (1 / 3 : ℝ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (hroot x ⟨hx.1, hx.2.le⟩) hb).trans hab
    have hbm : b * m x ≤ m x ^ (2 / 3 : ℝ) / 2 := by
      have hh := mul_le_mul_of_nonneg_right hbr hp.le
      rw [mul_assoc, hpower] at hh
      linarith
    have hineq := hode hx
    have hbound : (1 - 6 * c * deriv g x) * m x ^ (2 / 3 : ℝ) ≤ 0 := by
      nlinarith [he]
    have hbound' := nonpos_of_mul_nonpos_left hbound hp
    apply (div_le_iff₀ (by positivity : 0 < 6 * c)).2
    nlinarith
  have hlower (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (T - s) / (6 * c) ≤ g T := by
    have hgi : IntervalIntegrable (deriv g) volume s T := (hg.monotoneOn _).intervalIntegrable_deriv
    have hint := (hg.monotoneOn _).intervalIntegral_deriv_mem_uIcc (a := s) (b := T)
    rw [uIcc_of_le (sub_nonneg.mpr (hg hsT))] at hint
    have haeb : ∀ᵐ x ∂volume.restrict (Icc s T), 1 / (6 * c) ≤ deriv g x := by
      filter_upwards [ae_restrict_of_ae hderiv,
        ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ T} = 0))] with x hd hx hne
      exact hd ⟨hs.trans_le hx.1, hx.2.lt_of_ne hne⟩
    have hil := intervalIntegral.integral_mono_ae_restrict hsT
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ 1 / (6 * c)) volume s T)
      hgi haeb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hil
    simp only [mul_one_div] at hil
    have hgs : 0 ≤ g s := Real.rpow_nonneg (hm0 s) _
    linarith [hint.2]
  let s : ℕ → ℝ := fun n ↦ T / ((n : ℝ) + 1)
  have hs (n) : 0 < s n := by dsimp [s]; positivity
  have hsT (n) : s n ≤ T := by
    dsimp [s]
    exact div_le_self hT.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := T)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have hlim : Tendsto (fun n ↦ (T - s n) / (6 * c)) atTop (𝓝 (T / (6 * c))) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hs0).div_const (6 * c)
  exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds (fun n ↦ hlower (s n) (hs n) (hsT n))

theorem monotone_density_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    (T / (6 * c)) ^ 3 ≤ m T := by
  have hh := monotone_density_root_lower hm hm0 hT hb hc hab hpos hroot hode
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ T / (6 * c)) hh 3
  have he : (m T ^ (1 / 3 : ℝ)) ^ 3 = m T := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (hm0 T) (by norm_num : (3 : ℕ) ≠ 0)
  rwa [he] at hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_volume_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (∀ s : ℝ, 0 < s → 0 < torusVolume.real (E ∩ Metric.ball a s)) →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) := by
  obtain ⟨η, C, K, hη, hC, hK, hode⟩ := isMinimizerAt_sublevel_density_inequality hV hE hmin
  let R := min (1 / 4 : ℝ) (min (η / 16) (1 / (48 * (C + 1))))
  let c := (1 / (288 * K)) ^ 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨R, c, hR, hc, ?_⟩
  intro a r hr hrR hsupport
  have hrsmall : r ≤ 1 / 4 := hrR.trans (min_le_left _ _)
  have hrη : r ≤ η / 16 := hrR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r ≤ 1 / (48 * (C + 1)) := hrR.trans ((min_le_right _ _).trans (min_le_right _ _))
  let q := localRadialSquared a
  let m := sublevelVolume E q
  have hm : Monotone m := sublevelVolume_mono E q
  have hm0 (t) : 0 ≤ m t := ENNReal.toReal_nonneg
  have hupper {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ (2 * r) ^ 3 :=
    sublevelVolume_localRadialSquared_le E a hr.le hrsmall ht
  have hroot {t : ℝ} (ht : t ≤ r ^ 2) : m t ^ (1 / 3 : ℝ) ≤ 2 * r := by
    have hh := Real.rpow_le_rpow (hm0 t) (hupper ht) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have he : ((2 * r) ^ 3) ^ (1 / 3 : ℝ) = 2 * r := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 2 * r) (by norm_num : (3 : ℕ) ≠ 0)
    rwa [he] at hh
  have heta {t : ℝ} (ht : t ≤ r ^ 2) : m t < η := by
    have hrpow : r ^ 3 ≤ r := by
      have hr1 : r ≤ 1 := by linarith
      have := pow_le_pow_left₀ hr.le hr1 2
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr this)]
    have hu := hupper ht
    nlinarith
  have hhalf {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ 1 / 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * r)
      (show 2 * r ≤ 1 / 2 by linarith) 3
    norm_num at hp
    linarith [hupper ht]
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 (r ^ 2)) : 0 < m t := by
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hsr : Real.sqrt t ≤ r := (Real.sqrt_le_iff).2 ⟨hr.le, ht.2⟩
    have he : m t = torusVolume.real (E ∩ Metric.ball a (Real.sqrt t)) := by
      change torusVolume.real (E ∩ sublevelRegion q t) = _
      have hh := sublevelRegion_localRadialSquared a hs0.le (hsr.trans hrsmall)
      rw [Real.sq_sqrt ht.1.le] at hh
      rw [hh]
    rw [he]
    exact hsupport _ hs0
  have haeb : ∀ᵐ t : ℝ, t ∈ Ioo 0 (r ^ 2) →
      m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + (48 * K * r) * deriv m t := by
    filter_upwards [hode q (localRadialSquared_contDiff a) (localRadialSquared_periodic a)] with t ht
    intro htr
    have hgrad (x : Cover) (hx : q x < t) : ‖gradient q x‖ ≤ 2 * r :=
      norm_gradient_localRadialSquared a hr.le hrsmall x (hx.trans htr.2)
    have hh := ht (2 * r) hgrad (heta htr.2.le) (hhalf htr.2.le)
    change m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + 24 * K * (2 * r) * deriv m t at hh
    nlinarith [hh]
  have hab : (12 * C) * (2 * r) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 48 * (C + 1))).1 hrC
    nlinarith
  have hlower := monotone_density_lower hm hm0 (sq_pos_of_pos hr)
    (show 0 ≤ 12 * C by positivity) (show 0 < 48 * K * r by positivity) hab hpos
    (fun t ht ↦ hroot ht.2) haeb
  have he : (r ^ 2 / (6 * (48 * K * r))) ^ 3 = c * r ^ 3 := by
    dsimp only [c]
    field_simp
    ring
  rw [he] at hlower
  change _ ≤ torusVolume.real (E ∩ sublevelRegion (localRadialSquared a) (r ^ 2)) at hlower
  rwa [sublevelRegion_localRadialSquared a hr.le hrsmall] at hlower

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def volumeSupport (E : Set Torus) : Set Torus := (torusVolume.restrict E).support

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma volumeSupport_union_compl (E : Set Torus) (hE : MeasurableSet E) :
    volumeSupport E ∪ volumeSupport Eᶜ = univ := by
  rw [volumeSupport, volumeSupport, ← Measure.support_add,
    Measure.restrict_add_restrict_compl hE, Measure.support_eq_univ]

theorem isMinimizerAt_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
      ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) ∧
      c * r ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a r) := by
  obtain ⟨R₁, c₁, hR₁, hc₁, hd₁⟩ := isMinimizerAt_volume_density hV hE hmin
  have hVc : 1 - V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2], by linarith [hV.1]⟩
  obtain ⟨R₂, c₂, hR₂, hc₂, hd₂⟩ := isMinimizerAt_volume_density hVc hE.compl
    ((isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hmin)
  refine ⟨min R₁ R₂, min c₁ c₂, lt_min hR₁ hR₂, lt_min hc₁ hc₂, ?_⟩
  intro a ha r hr hrR
  constructor
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hd₁ a r hr (hrR.trans (min_le_left _ _)) ((mem_volumeSupport_iff E a).1 ha.1))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
      (hd₂ a r hr (hrR.trans (min_le_right _ _)) ((mem_volumeSupport_iff Eᶜ a).1 ha.2))

instance torusVolume_doubling : IsUnifLocDoublingMeasure torusVolume := by
  refine ⟨27, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))] with r hr hs a
  have hrpos : 0 < r := hr
  change r < 1 / 6 at hs
  calc
    torusVolume (Metric.closedBall a (2 * r)) ≤ torusVolume (Metric.ball a (3 * r)) :=
      measure_mono (Metric.closedBall_subset_ball (by linarith))
    _ = (27 : ℝ≥0∞) * torusVolume (Metric.ball a r) := by
      rw [volume_torusBall a (by positivity) (by linarith),
        volume_torusBall a hrpos.le (by linarith), ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
      congr 1
      ring
    _ ≤ (27 : ℝ≥0∞) * torusVolume (Metric.closedBall a r) := by
      gcongr
      exact Metric.ball_subset_closedBall

lemma realVolume_closedBall_le (a : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4) :
    torusVolume.real (Metric.closedBall a r) ≤ 64 * r ^ 3 := by
  calc
    _ ≤ torusVolume.real (Metric.ball a (2 * r)) :=
      measureReal_mono (Metric.closedBall_subset_ball (by linarith))
    _ = (2 * r) ^ 3 * (Real.pi * 4 / 3) := by
      rw [Measure.real_def, volume_torusBall a (by positivity) (by linarith),
        ENNReal.toReal_ofReal (by positivity)]
    _ ≤ _ := by nlinarith [Real.pi_lt_four, pow_pos hr 3]

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

lemma volumeSupport_ae_eq_of_density {E : Set Torus} (hE : MeasurableSet E)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hd : ∀ a ∈ volumeSupport E, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r)) :
    volumeSupport E =ᵐ[torusVolume] E := by
  have hs : ∀ᵐ a ∂torusVolume, a ∈ E → a ∈ volumeSupport E :=
    (ae_restrict_iff' hE).1 Measure.support_mem_ae
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average torusVolume
    (integrable_characteristic hE).locallyIntegrable 1
  filter_upwards [hs, hdiff] with a has had
  apply propext
  refine ⟨fun ha ↦ ?_, has⟩
  by_contra hnot
  change a ∉ E at hnot
  have hchar : characteristic E a = 0 := by simp [characteristic, hnot]
  have ht : Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, characteristic E x ∂torusVolume)
      (𝓝[>] 0) (𝓝 0) := by
    have hh := had (fun _ : ℝ ↦ a) id tendsto_id
      (show ∀ᶠ r : ℝ in 𝓝[>] 0, a ∈ Metric.closedBall a (1 * id r) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        change a ∈ Metric.closedBall a (1 * r)
        rw [one_mul]
        exact Metric.mem_closedBall_self (le_of_lt hr))
    rw [hchar] at hh
    convert! hh using 1
  have hlower : ∀ᶠ r : ℝ in 𝓝[>] 0,
      c / 64 ≤ ⨍ x in Metric.closedBall a r, characteristic E x ∂torusVolume := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with r hr hrR hr4
    have hrpos : 0 < r := hr
    have hb := hd a ha r hrpos hrR.le
    have hmono : torusVolume.real (E ∩ Metric.ball a r) ≤
        torusVolume.real (E ∩ Metric.closedBall a r) :=
      measureReal_mono (inter_subset_inter_right E Metric.ball_subset_closedBall)
    have hpos : 0 < torusVolume.real (Metric.closedBall a r) :=
      (mul_pos hc (pow_pos hrpos 3)).trans_le
        (hb.trans (hmono.trans (measureReal_mono inter_subset_right)))
    rw [setAverage_eq, setIntegral_characteristic hE _ Metric.isClosed_closedBall.measurableSet,
      smul_eq_mul, ← div_eq_inv_mul]
    apply (le_div_iff₀ hpos).2
    have hh := mul_le_mul_of_nonneg_left (realVolume_closedBall_le a hrpos hr4.le)
      (show 0 ≤ c / 64 by positivity)
    nlinarith
  have hh := ge_of_tendsto ht hlower
  linarith

def openRepresentative (E : Set Torus) : Set Torus := (volumeSupport Eᶜ)ᶜ

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

theorem isMinimizerAt_openRepresentative_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    openRepresentative E =ᵐ[torusVolume] E := by
  have hVc : 1 - V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2], by linarith [hV.1]⟩
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_volume_density hVc hE.compl
    ((isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hmin)
  have hh := volumeSupport_ae_eq_of_density hE.compl hR hc
    (fun a ha r hr hs ↦ hd a r hr hs ((mem_volumeSupport_iff Eᶜ a).1 ha))
  simpa only [openRepresentative, compl_compl] using hh.compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

lemma volumeSupport_eq_closure {E : Set Torus} (hE : IsOpen E) :
    volumeSupport E = closure E := by
  apply Subset.antisymm
  · exact Measure.support_restrict_subset.trans inter_subset_left
  · apply closure_minimal _ (isClosed_volumeSupport E)
    have hh := Measure.interior_inter_support (μ := torusVolume) (s := E)
    change E ⊆ (torusVolume.restrict E).support
    simpa only [hE.interior_eq, Measure.support_eq_univ, inter_univ] using hh

lemma isMinimizerAt_closure_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E) = volumeSupport E := by
  rw [← volumeSupport_eq_closure (isOpen_openRepresentative E)]
  exact volumeSupport_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)

lemma isMinimizerAt_frontier_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative E) = volumeSupport E ∩ volumeSupport Eᶜ := by
  rw [frontier, (isOpen_openRepresentative E).interior_eq,
    isMinimizerAt_closure_openRepresentative hV hE hmin]
  simp only [openRepresentative, sdiff_eq, compl_compl]

theorem isMinimizerAt_volume_frontier_eq_zero {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    torusVolume (frontier (openRepresentative E)) = 0 := by
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_volume_density hV hE hmin
  have hs := volumeSupport_ae_eq_of_density hE hR hc
    (fun a ha r hr hh ↦ hd a r hr hh ((mem_volumeSupport_iff E a).1 ha))
  have ho := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hae : frontier (openRepresentative E) =ᵐ[torusVolume] (∅ : Set Torus) := by
    rw [frontier, (isOpen_openRepresentative E).interior_eq,
      isMinimizerAt_closure_openRepresentative hV hE hmin]
    filter_upwards [hs, ho] with x hx hy
    change ((x ∈ volumeSupport E) ∧ x ∉ openRepresentative E) = False
    change (x ∈ volumeSupport E) = (x ∈ E) at hx
    change (x ∈ openRepresentative E) = (x ∈ E) at hy
    simp only [hx, hy, and_not_self]
  rw [measure_congr hae, measure_empty]

theorem isMinimizerAt_exists_open_density_representative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ U : Set Torus, IsOpen U ∧ U =ᵐ[torusVolume] E ∧
      IsMinimizerAt V U ∧ torusVolume (frontier U) = 0 ∧
      ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a ∈ frontier U,
        ∀ r : ℝ, 0 < r → r ≤ R →
          c * r ^ 3 ≤ torusVolume.real (U ∩ Metric.ball a r) ∧
          c * r ^ 3 ≤ torusVolume.real (Uᶜ ∩ Metric.ball a r) := by
  let U := openRepresentative E
  have hu := isMinimizerAt_openRepresentative_ae hV hE hmin
  refine ⟨U, isOpen_openRepresentative E, hu, (isMinimizerAt_congr_ae hu).2 hmin,
    isMinimizerAt_volume_frontier_eq_zero hV hE hmin, ?_⟩
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  refine ⟨R, c, hR, hc, ?_⟩
  intro a ha r hr hs
  have ha' : a ∈ volumeSupport E ∩ volumeSupport Eᶜ := by
    rwa [isMinimizerAt_frontier_openRepresentative hV hE hmin] at ha
  have hh := hd a ha' r hr hs
  have he₁ : torusVolume.real (U ∩ Metric.ball a r) = torusVolume.real (E ∩ Metric.ball a r) :=
    congrArg ENNReal.toReal (measure_congr (hu.inter EventuallyEq.rfl))
  have he₂ : torusVolume.real (Uᶜ ∩ Metric.ball a r) = torusVolume.real (Eᶜ ∩ Metric.ball a r) :=
    congrArg ENNReal.toReal (measure_congr (hu.compl.inter EventuallyEq.rfl))
  rwa [he₁, he₂]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalProjection (z : NormalBundle) : Torus := quotientMap z.1

lemma normalProjection_continuous : Continuous normalProjection :=
  continuous_quotientMap.comp (continuous_subtype_val.comp continuous_fst)

def spatialNormalMeasure (μ : FiniteMeasure NormalBundle) : FiniteMeasure Torus :=
  μ.map normalProjection

lemma integral_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) {f : Torus → ℝ}
    (hf : Measurable f) :
    (∫ x, f x ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, f (normalProjection z) ∂(μ : Measure NormalBundle) := by
  change (∫ x, f x ∂Measure.map normalProjection (μ : Measure NormalBundle)) = _
  exact integral_map normalProjection_continuous.measurable.aemeasurable hf.aestronglyMeasurable

lemma integral_spatialNormalMeasure_periodic (μ : FiniteMeasure NormalBundle)
    {w : Cover → ℝ} (hw : Continuous w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) :
    (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, w z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_spatialNormalMeasure μ (f := fun x ↦ w (representative x))
    (hw.measurable.comp measurable_representative)]
  congr 1
  ext z
  exact periodic_representative hp z.1

lemma spatialNormalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) := by
  rw [integral_spatialNormalMeasure_periodic μ hw.continuous hp]
  exact normalMeasure_weightedPerimeter hμ hw hp hn

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma sublevelCutoff_eq_one {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : q x ≤ t - ε) : sublevelCutoff q t ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by linarith)

lemma divergence_cutoff_zero {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {t ε : ℝ} (hε : 0 < ε) {x : Cover} (hx : t ≤ q x) :
    divergence (fun y ↦ sublevelCutoff q t ε y • F y) x = 0 := by
  rw [divergence_smul_function ((sublevelCutoff_contDiff hq t ε).differentiable (by simp) x)
    (hF.differentiable (by simp) x), sublevelCutoff_eq_zero hε hx,
    sublevelCutoff_gradient_zero (hq.differentiable (by simp)) hε t x (Or.inr hx)]
  simp

lemma admissible_sublevelCutoff {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {F : Cover → Cover}
    (hF : AdmissibleField F) (t ε : ℝ) :
    AdmissibleField (fun x ↦ sublevelCutoff q t ε x • F x) := by
  have hh := admissible_convex_cutoff (sublevelCutoff_contDiff hq t ε)
    (sublevelCutoff_periodic hp t ε) (sublevelCutoff_mem_Icc q t ε) hF admissible_zero
  simpa only [smul_zero, add_zero] using hh

lemma weightedPerimeter_sublevelCutoff_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {t ε : ℝ} (hε : 0 < ε) :
    weightedPerimeter E (sublevelCutoff q t ε) ≤ perimeter (E ∩ sublevelRegion q t) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have he : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ sublevelRegion q t),
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))
      (inter_subset_inter_right _ (preimage_mono inter_subset_left))
    intro x hx
    apply divergence_cutoff_zero hq hF.1 hε
    by_contra hn
    apply hx.2
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    exact (mem_sublevelRegion_quotient hp t x).2 (lt_of_not_ge hn)
  rw [he]
  exact le_iSup₂_of_le (fun x ↦ sublevelCutoff q t ε x • F x)
    (admissible_sublevelCutoff hq hp hF t ε) le_rfl

lemma spatialNormalMeasure_sublevel_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {s t : ℝ} (hst : s < t)
    (hP : perimeter (E ∩ sublevelRegion q t) ≠ ⊤) :
    (spatialNormalMeasure μ : Measure Torus).real (sublevelRegion q s) ≤
      (perimeter (E ∩ sublevelRegion q t)).toReal := by
  let σ : Measure Torus := spatialNormalMeasure μ
  let w := sublevelCutoff q t (t - s)
  let B := sublevelRegion q s
  have hB : MeasurableSet B := measurableSet_sublevelRegion hq.continuous.measurable s
  have hwb (x : Cover) : w x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (t - s) x
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := sublevelCutoff_contDiff hq t (t - s)
  have hwp : ∀ n x, w (x + latticeVector n) = w x := sublevelCutoff_periodic hp t (t - s)
  have hi : Integrable (fun x ↦ w (representative x)) σ :=
    Integrable.of_bound (hw.continuous.measurable.comp measurable_representative).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hwb _).1]
        exact (hwb _).2)
  have hminor (x : Torus) : B.indicator (fun _ ↦ (1 : ℝ)) x ≤ w (representative x) := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact le_of_eq (sublevelCutoff_eq_one (sub_pos.mpr hst) (by
        have hh : q (representative x) < s := hx
        linarith)).symm
    · rw [indicator_of_notMem hx]
      exact (hwb _).1
  have hm : σ.real B ≤ ∫ x, w (representative x) ∂σ := by
    have hh := integral_mono ((integrable_const (1 : ℝ)).indicator hB) hi hminor
    simpa only [integral_indicator hB, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] using hh
  have hpbound := weightedPerimeter_sublevelCutoff_le hE hq hp (t := t) (sub_pos.mpr hst)
  rw [spatialNormalMeasure_weightedPerimeter hμ hw hwp (fun x ↦ (hwb x).1)] at hpbound
  have hnonneg : 0 ≤ ∫ x, w (representative x) ∂σ := integral_nonneg fun x ↦ (hwb _).1
  have hh := ENNReal.toReal_mono hP hpbound
  rw [ENNReal.toReal_ofReal hnonneg] at hh
  exact hm.trans hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma monotone_exists_deriv_le {m : ℝ → ℝ} (hm : Monotone m) {a b M : ℝ}
    (hab : a < b) (hbound : m b - m a < M * (b - a)) :
    ∃ t ∈ Ioo a b, DifferentiableAt ℝ m t ∧ deriv m t ≤ M := by
  by_contra! hn
  have haeb : ∀ᵐ x ∂volume.restrict (Icc a b), M ≤ deriv m x := by
    filter_upwards [ae_restrict_of_ae hm.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff]),
      ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff])] with x hx hxab hxa hxb
    exact le_of_lt (hn x ⟨hxab.1.lt_of_ne hxa.symm, hxab.2.lt_of_ne hxb⟩ hx)
  have hi := intervalIntegral.integral_mono_ae_restrict hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ M) volume a b)
    ((hm.monotoneOn _).intervalIntegrable_deriv) haeb
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hu := (hm.monotoneOn _).intervalIntegral_deriv_mem_uIcc (a := a) (b := b)
  rw [uIcc_of_le (sub_nonneg.mpr (hm hab.le))] at hu
  linarith [hu.2]

theorem isMinimizerAt_perimeter_upper_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R A : ℝ, 0 < R ∧ 0 < A ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
        (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2 := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := isMinimizerAt_sublevel_comparison hV hE hmin
  obtain ⟨K, hK, hKd⟩ := smoothTransition_exists_deriv_bound
  let R := min (1 / 8 : ℝ) (η / 128)
  let A := 64 * C + 512 * K
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨R, A, hR, hA, ?_⟩
  intro μ hμ a r hr hrR
  have hrsmall : r ≤ 1 / 8 := hrR.trans (min_le_left _ _)
  have hrη : r ≤ η / 128 := hrR.trans (min_le_right _ _)
  have hr2 : 0 ≤ 2 * r := by positivity
  have hr2small : 2 * r ≤ 1 / 4 := by linarith
  have hrpow : r ^ 3 ≤ r := by
    have hh := pow_le_pow_left₀ hr.le (show r ≤ 1 by linarith) 2
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hh)]
  have hrpow2 : r ^ 3 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1 - r by linarith)]
  let q := localRadialSquared a
  let m := sublevelVolume E q
  have hm : Monotone m := sublevelVolume_mono E q
  have hm0 (t) : 0 ≤ m t := ENNReal.toReal_nonneg
  have hupper {t : ℝ} (ht : t ≤ (2 * r) ^ 2) : m t ≤ 64 * r ^ 3 := by
    have hh := sublevelVolume_localRadialSquared_le E a hr2 hr2small ht
    change m t ≤ (2 * (2 * r)) ^ 3 at hh
    nlinarith
  have hinterval : r ^ 2 < (2 * r) ^ 2 := by nlinarith [sq_pos_of_pos hr]
  have hdiff : m ((2 * r) ^ 2) - m (r ^ 2) < (64 * r) * ((2 * r) ^ 2 - r ^ 2) := by
    have hh := hupper (le_refl ((2 * r) ^ 2))
    have hp : 0 < r ^ 3 := pow_pos hr _
    nlinarith [hm0 (r ^ 2)]
  obtain ⟨t, ht, htd, hd⟩ := monotone_exists_deriv_le hm hinterval hdiff
  have hgrad (x : Cover) (hx : q x < t) : ‖gradient q x‖ ≤ 4 * r := by
    have hh := norm_gradient_localRadialSquared a hr2 hr2small x (hx.trans ht.2)
    change ‖gradient q x‖ ≤ 2 * (2 * r) at hh
    linarith
  have heta : m t < η := by
    have hh := hupper ht.2.le
    nlinarith
  have hcut := (perimeter_sublevel_partition hE hmin.1.2.ne
    (localRadialSquared_contDiff a) (localRadialSquared_periodic a) hKd hgrad htd.hasDerivAt).1
  have hh := hcomp q (localRadialSquared_contDiff a) (localRadialSquared_periodic a)
    K (4 * r) t (deriv m t) hKd hgrad htd.hasDerivAt heta
  have hmass := spatialNormalMeasure_sublevel_le hE hμ (localRadialSquared_contDiff a)
    (localRadialSquared_periodic a) ht.1 hcut.2.ne
  rw [sublevelRegion_localRadialSquared a hr.le (by linarith : r ≤ 1 / 4)] at hmass
  apply le_trans hmass
  apply le_trans hh
  change C * m t + 2 * K * (4 * r) * deriv m t ≤ A * r ^ 2
  have hCm := mul_le_mul_of_nonneg_left (hupper ht.2.le) hC
  have hCd := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * K * (4 * r) by positivity)
  have hCr := mul_le_mul_of_nonneg_left hrpow2 (show 0 ≤ 64 * C by positivity)
  dsimp [A]
  nlinarith

end CubicTorus

end
end

end

end OAI
