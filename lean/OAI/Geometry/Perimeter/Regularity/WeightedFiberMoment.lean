import OAI.Geometry.Perimeter.Regularity.PhaseMomentLimit
import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem mollified_fiber_weighted_defect {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : ∀ y, 0 ≤ φ y)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hp : ∀ x, 0 ≤ k x) (hu : ∫ x, k x = 1)
    {a b ε R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+ε < b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0))
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+ε ≤ R) :
    let q := phaseMollification E k
    let H := fun y : normalPlane v ↦ -b+∫ s in (-b)..b, q ((y:Euc n)+s•v)
    let M := ∫ x, normalWindowTest v φ b 2 x * (-fderiv ℝ q x v)
    0 ≤ M - ∫ y in tsupport φ, φ y*(H y)^2 ∧
    M - ∫ y in tsupport φ, φ y*(H y)^2 ≤
      4*b*(∫ x, normalWindowTest v φ b 0 x * (q x*(1-q x))) +
      8*b^2*(∫ x, normalWindowTest v φ b 0 x * max (fderiv ℝ q x v) 0) := by
  dsimp only
  let q := phaseMollification E k
  have hq : Continuous q := (phaseMollification_contDiff hE hk hc).continuous
  have hd : Continuous (fun x ↦ fderiv ℝ q x v) :=
    ((phaseMollification_contDiff hE hk hc).continuous_fderiv (by simp)).clm_apply continuous_const
  have hiM := normalWindowTest_integral hv hφ hcφ hb 2 hd.neg
  have hiD := normalWindowTest_integral hv hφ hcφ hb 0 (hq.mul ((continuous_const (y := (1:ℝ))).sub hq))
  have hiP := normalWindowTest_integral hv hφ hcφ hb 0 (hd.max (continuous_const (y := (0:ℝ))))
  dsimp only [q,Pi.neg_apply,Pi.mul_apply,Pi.sub_apply] at hiM hiD hiP
  rw [hiM,hiD,hiP]
  simp only [pow_zero,one_mul]
  simp_rw [← mollifiedNormalProfile_deriv hE hk hc v]
  let A := fun y : normalPlane v ↦ ∫ s in (-b)..b,
    s^2*(-deriv (mollifiedNormalProfile E k v y) s)
  let B := fun y : normalPlane v ↦ (-b+∫ s in (-b)..b, q ((y:Euc n)+s•v))^2
  let D := fun y : normalPlane v ↦ ∫ s in (-b)..b, q ((y:Euc n)+s•v)*(1-q ((y:Euc n)+s•v))
  let P := fun y : normalPlane v ↦ ∫ s in (-b)..b, max (deriv (mollifiedNormalProfile E k v y) s) 0
  have hA : Continuous A := by
    have hm : Continuous (fun x ↦ (inner ℝ v x)^2*(-fderiv ℝ q x v)) :=
      ((continuous_const.inner continuous_id).pow 2).mul hd.neg
    have h := continuous_profile_integral (v := v) _ hm (-b) b
    dsimp only [q] at h
    simp_rw [normal_fiber_inner hv,← mollifiedNormalProfile_deriv hE hk hc v] at h
    exact h
  have hB : Continuous B :=
    (continuous_const.add (continuous_profile_integral (v := v) q hq (-b) b)).pow 2
  have hD : Continuous D := continuous_profile_integral (v := v) _
    (hq.mul ((continuous_const (y := (1:ℝ))).sub hq)) (-b) b
  have hP : Continuous P := by
    have h := continuous_profile_integral (v := v) _ (hd.max (continuous_const (y := (0:ℝ)))) (-b) b
    dsimp only [q] at h
    simp_rw [← mollifiedNormalProfile_deriv hE hk hc v] at h
    exact h
  have hAi : IntegrableOn (fun y ↦ φ y*A y) (tsupport φ) volume :=
    (hφ.mul hA).continuousOn.integrableOn_compact hcφ
  have hBi : IntegrableOn (fun y ↦ φ y*B y) (tsupport φ) volume :=
    (hφ.mul hB).continuousOn.integrableOn_compact hcφ
  have hDi : IntegrableOn (fun y ↦ φ y*D y) (tsupport φ) volume :=
    (hφ.mul hD).continuousOn.integrableOn_compact hcφ
  have hPi : IntegrableOn (fun y ↦ φ y*P y) (tsupport φ) volume :=
    (hφ.mul hP).continuousOn.integrableOn_compact hcφ
  change 0 ≤ (∫ y in tsupport φ, φ y*A y)-(∫ y in tsupport φ, φ y*B y) ∧
    (∫ y in tsupport φ, φ y*A y)-(∫ y in tsupport φ, φ y*B y) ≤
      4*b*(∫ y in tsupport φ, φ y*D y)+8*b^2*(∫ y in tsupport φ, φ y*P y)
  rw [← integral_sub hAi hBi,← integral_const_mul,← integral_const_mul,
    ← integral_add (hDi.const_mul _) (hPi.const_mul _)]
  have hh (y : normalPlane v) (hy : y ∈ tsupport φ) :=
    mollifiedNormalProfile_flux_defect hE hv hk hc hp hu ha hb hab hs hphase y (hKR y hy)
  constructor
  · apply setIntegral_nonneg hcφ.measurableSet
    intro y hy
    have h := mul_nonneg (hpφ y) (hh y hy).1
    change 0 ≤ φ y*A y-φ y*B y
    change 0 ≤ φ y*(A y-B y) at h
    nlinarith only [h]
  · apply setIntegral_mono_on (hAi.sub hBi) ((hDi.const_mul _).add (hPi.const_mul _))
      hcφ.measurableSet
    intro y hy
    have h := mul_le_mul_of_nonneg_left (hh y hy).2 (hpφ y)
    change φ y*A y-φ y*B y ≤ 4*b*(φ y*D y)+8*b^2*(φ y*P y)
    change φ y*(A y-B y) ≤ φ y*(4*b*D y+8*b^2*P y) at h
    nlinarith only [h]

theorem normalWindowTest_diffuse_tendsto_zero {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (b : ℝ) :
    Tendsto (fun j ↦ ∫ x, normalWindowTest v φ b 0 x *
      (phaseMollification E ((c1Mollifier j).normed volume) x *
        (1-phaseMollification E ((c1Mollifier j).normed volume) x))) atTop (𝓝 0) := by
  have hi := normalWindowTest_integrable hv hφ hcφ b 0
  have ht : ∀ᵐ x ∂volume, Tendsto (fun j ↦ normalWindowTest v φ b 0 x *
      (phaseMollification E ((c1Mollifier j).normed volume) x *
        (1-phaseMollification E ((c1Mollifier j).normed volume) x))) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [phaseMollification_ae_tendsto hE] with x hx
    convert tendsto_const_nhds.mul (hx.mul (tendsto_const_nhds.sub hx)) using 1
    by_cases he : x ∈ E <;> simp [he]
  have h := tendsto_integral_of_dominated_convergence (fun x ↦ ‖normalWindowTest v φ b 0 x‖)
    (fun j ↦ (normalWindowTest_measurable hφ b 0).aestronglyMeasurable.mul
      (((phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous.mul
          (continuous_const.sub (phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
            (c1Mollifier j).hasCompactSupport_normed).continuous)).aestronglyMeasurable))
    hi.norm (fun j ↦ ae_of_all _ fun x ↦ ?_) ht
  · simpa only [integral_zero,Pi.mul_apply,Pi.sub_apply] using h
  · obtain ⟨h0,h1⟩ := phaseMollification_c1_mem_Icc hE j x
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [norm_mul]
    have hb : ‖phaseMollification E ((c1Mollifier j).normed volume) x *
        (1-phaseMollification E ((c1Mollifier j).normed volume) x)‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1))]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_one _)

theorem mollified_fiber_weighted_height_square_tendsto {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun j ↦ ∫ y in tsupport φ, φ y*
      (-b+∫ s in (-b)..b, phaseMollification E ((c1Mollifier j).normed volume)
        ((y:Euc n)+s•v))^2) atTop
      (𝓝 (∫ y in tsupport φ, φ y*(exactFiberHeight E v b y)^2)) := by
  apply tendsto_integral_of_dominated_convergence (fun y ↦ ‖φ y‖*b^2)
  · intro j
    exact (hφ.mul ((continuous_const.add (continuous_profile_integral (v := v) _
      (phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous (-b) b)).pow 2)).aestronglyMeasurable
  · exact (hφ.continuousOn.integrableOn_compact hcφ).norm.mul_const _
  · intro j
    apply ae_of_all
    intro y
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h := interval_height_abs_le
      (((phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))).measurable)
      hb (fun s ↦ phaseMollification_c1_mem_Icc hE j ((y:Euc n)+s•v))
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs,Function.comp_def,Pi.add_apply,Pi.smul_apply,Pi.smul_apply',id_eq] using
      (sq_le_sq₀ (abs_nonneg _) hb).mpr h
  · filter_upwards [ae_restrict_of_ae (mollified_fiber_height_ae_tendsto hE hv hb)] with y hy
    exact tendsto_const_nhds.mul (hy.pow 2)

end RPISingularHarnack

end

end OAI
