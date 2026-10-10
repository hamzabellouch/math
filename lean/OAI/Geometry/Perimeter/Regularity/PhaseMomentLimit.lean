import OAI.Geometry.Perimeter.Regularity.FiberMomentIntegration

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem phaseMollification_c1_eq (E : Set (Euc n)) (j : ℕ) :
    phaseMollification E ((c1Mollifier j).normed volume) =
      c1Mollify (E.indicator (fun _ ↦ (1:ℝ))) j := by
  funext x
  rw [phaseMollification,convolution_eq_swap]
  change (∫ y, E.indicator (fun _ ↦ (1:ℝ)) (x-y) * (c1Mollifier j).normed volume y) = _
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ mul_comm _ _

theorem phaseMollification_ae_tendsto {E : Set (Euc n)} (hE : MeasurableSet E) :
    ∀ᵐ x ∂volume, Tendsto (fun j ↦ phaseMollification E ((c1Mollifier j).normed volume) x)
      atTop (𝓝 (E.indicator (fun _ ↦ (1:ℝ)) x)) := by
  simp_rw [phaseMollification_c1_eq]
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    c1Mollifier_radius_tendsto (K := 2) _ ((locallyIntegrable_const (1:ℝ)).indicator hE)
  apply Eventually.of_forall
  intro j
  dsimp [c1Mollifier]
  linarith

theorem phaseMollification_c1_mem_Icc {E : Set (Euc n)} (hE : MeasurableSet E)
    (j : ℕ) (x : Euc n) :
    phaseMollification E ((c1Mollifier j).normed volume) x ∈ Icc (0:ℝ) 1 :=
  phaseMollification_mem_Icc hE (c1Mollifier j).integrable_normed
    (c1Mollifier j).nonneg_normed (c1Mollifier j).integral_normed x

theorem phaseMollification_diffuse_tendsto_zero {E : Set (Euc n)} (hE : MeasurableSet E)
    (K : Set (Euc n)) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      phaseMollification E ((c1Mollifier j).normed volume) x *
        (1-phaseMollification E ((c1Mollifier j).normed volume) x)) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun j ↦
      phaseMollification E ((c1Mollifier j).normed volume) x *
        (1-phaseMollification E ((c1Mollifier j).normed volume) x)) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_of_ae (phaseMollification_ae_tendsto hE)] with x hx
    convert hx.mul (tendsto_const_nhds.sub hx) using 1
    by_cases he : x ∈ E <;> simp [he]
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict K) (fun _ ↦ (1:ℝ))
    (fun j ↦ ((phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
      (c1Mollifier j).hasCompactSupport_normed).continuous.mul
        (continuous_const.sub (phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
          (c1Mollifier j).hasCompactSupport_normed).continuous)).aestronglyMeasurable)
    (integrable_const _) (fun j ↦ ae_of_all _ fun x ↦ ?_) hlim
  · simpa only [integral_zero,Pi.mul_apply,Pi.sub_apply] using h
  · obtain ⟨h0,h1⟩ := phaseMollification_c1_mem_Icc hE j x
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1))]
    nlinarith

def exactFiberHeight (E : Set (Euc n)) (v : Euc n) (b : ℝ)
    (y : normalPlane v) : ℝ :=
  -b+∫ s in (-b)..b, E.indicator (fun _ ↦ (1:ℝ)) ((y:Euc n)+s•v)

theorem phaseMollification_fiber_ae_tendsto {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) :
    ∀ᵐ y : normalPlane v ∂volume, ∀ᵐ s : ℝ ∂volume,
      Tendsto (fun j ↦ phaseMollification E ((c1Mollifier j).normed volume)
        ((y:Euc n)+s•v)) atTop (𝓝 (E.indicator (fun _ ↦ (1:ℝ)) ((y:Euc n)+s•v))) := by
  have ht := (normalCoordinates_measurePreserving v hv).quasiMeasurePreserving.ae
    (phaseMollification_ae_tendsto hE)
  change ∀ᵐ z : normalPlane v × ℝ ∂volume.prod volume, _ at ht
  exact Measure.ae_ae_of_ae_prod ht

theorem mollified_fiber_height_ae_tendsto {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ y : normalPlane v ∂volume, Tendsto (fun j ↦
      -b+∫ s in (-b)..b, phaseMollification E ((c1Mollifier j).normed volume)
        ((y:Euc n)+s•v)) atTop (𝓝 (exactFiberHeight E v b y)) := by
  filter_upwards [phaseMollification_fiber_ae_tendsto hE hv] with y hy
  let F : ℕ → ℝ → ℝ := fun j ↦ mollifiedNormalProfile E ((c1Mollifier j).normed volume) v y
  let f : ℝ → ℝ := fun s ↦ E.indicator (fun _ ↦ (1:ℝ)) ((y:Euc n)+s•v)
  have hm (j : ℕ) : AEStronglyMeasurable (F j) (volume.restrict (Ioc (-b) b)) :=
    (mollifiedNormalProfile_contDiff hE (c1Mollifier j).contDiff_normed
      (c1Mollifier j).hasCompactSupport_normed v y).continuous.aestronglyMeasurable
  have hbd (j : ℕ) : ∀ᵐ s ∂volume.restrict (Ioc (-b) b), ‖F j s‖ ≤ 1 := by
    apply ae_of_all
    intro s
    obtain ⟨h0,h1⟩ := phaseMollification_c1_mem_Icc hE j ((y:Euc n)+s•v)
    change ‖phaseMollification E ((c1Mollifier j).normed volume) ((y:Euc n)+s•v)‖ ≤ 1
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0] using h1
  have hlim : ∀ᵐ s ∂volume.restrict (Ioc (-b) b), Tendsto (fun j ↦ F j s) atTop (𝓝 (f s)) :=
    ae_restrict_of_ae hy
  have h : Tendsto (fun j ↦ ∫ s in Ioc (-b) b, F j s) atTop
      (𝓝 (∫ s in Ioc (-b) b, f s)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hm (integrable_const _) hbd hlim
  have hadd := (tendsto_const_nhds (x := -b)).add h
  simpa only [exactFiberHeight,intervalIntegral.integral_of_le (by linarith : -b ≤ b),
    F,f,mollifiedNormalProfile] using hadd

theorem interval_height_abs_le {q : ℝ → ℝ} (hq : Measurable q) {b : ℝ}
    (hb : 0 ≤ b) (hbound : ∀ s, q s ∈ Icc (0:ℝ) 1) :
    |-b+∫ s in (-b)..b, q s| ≤ b := by
  have hi : IntervalIntegrable q volume (-b) b := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun hq.aestronglyMeasurable
    apply ae_of_all
    intro s
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hbound s).1,abs_one] using (hbound s).2
  have h0 : 0 ≤ ∫ s in (-b)..b, q s :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ ↦ (hbound s).1
  have h1 : (∫ s in (-b)..b, q s) ≤ 2*b := by
    calc
      _ ≤ ∫ s in (-b)..b, (1:ℝ) := intervalIntegral.integral_mono_on
        (by linarith) hi intervalIntegrable_const (fun s _ ↦ (hbound s).2)
      _ = _ := by simp; ring
  rw [abs_le]
  constructor <;> linarith

theorem mollified_fiber_height_square_tendsto {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {b : ℝ} (hb : 0 ≤ b)
    (K : Set (normalPlane v)) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ y in K,
      (-b+∫ s in (-b)..b, phaseMollification E ((c1Mollifier j).normed volume)
        ((y:Euc n)+s•v))^2) atTop (𝓝 (∫ y in K, (exactFiberHeight E v b y)^2)) := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ b^2)
  · intro j
    exact ((continuous_const.add (continuous_profile_integral (v := v) _
      (phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous (-b) b)).pow 2).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    apply ae_of_all
    intro y
    have h := interval_height_abs_le
      (((phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))).measurable)
      hb (fun s ↦ phaseMollification_c1_mem_Icc hE j ((y:Euc n)+s•v))
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs,Function.comp_def,Pi.add_apply,Pi.smul_apply,Pi.smul_apply',id_eq] using
      (sq_le_sq₀ (abs_nonneg _) hb).mpr h
  · filter_upwards [ae_restrict_of_ae (mollified_fiber_height_ae_tendsto hE hv hb)] with y hy
    exact hy.pow 2

end RPISingularHarnack

end

end OAI
