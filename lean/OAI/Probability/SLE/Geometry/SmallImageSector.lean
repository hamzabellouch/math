import OAI.Probability.SLE.Geometry.SmallImageSemicircle
import OAI.Probability.SLE.AngularLaws

namespace OAI

/-!
The central-sector extension of `es:good-semicircle`. The already proved
omitted-value estimate gives a universal constant `4096 * π` in place of the
sharper constant `6` in the manuscript; this suffices for the splice.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace SLEExactGauge.SmallImageSemicircle

lemma log_norm_fderiv_le_of_height
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {b : ℝ} (hb : 0 < b)
    {w : ℂ} (hw : b ≤ w.im) :
    DifferentiableAt ℝ (fun z => Real.log ‖F z - a‖) w ∧
      ‖fderiv ℝ (fun z => Real.log ‖F z - a‖) w‖ ≤ (128 * Real.pi) / b := by
  have hwH : 0 < w.im := hb.trans_le hw
  have hball : ball w b ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have hdist : ‖z - w‖ < b := mem_ball_iff_norm.mp hz
    have him := (le_abs_self (w.im - z.im)).trans
      (by simpa only [Complex.sub_im, abs_sub_comm] using Complex.abs_im_le_norm (z - w))
    change 0 < z.im
    linarith
  have hnot : a ∉ F '' ball w b := by
    rintro ⟨z, hz, he⟩
    exact ha z (hball hz) he
  have hbound := univalent_omitted_value_bound_ball hb (hF.mono hball) (hi.mono hball) a hnot
  have hFd : DifferentiableAt ℂ F w := hF.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hwH)
  have hn : F w - a ≠ 0 := sub_ne_zero.mpr (ha w hwH)
  have hnp : 0 < ‖F w - a‖ := norm_pos_iff.mpr hn
  refine ⟨(((hFd.restrictScalars ℝ).sub_const a).norm ℝ hn).log hnp.ne', ?_⟩
  have hlog := norm_fderiv_log_norm_div_le hFd a (by norm_num : (0 : ℝ) < 1) hn
  simp only [div_one] at hlog
  apply hlog.trans
  apply (div_le_div_iff₀ hnp hb).mpr
  nlinarith [hbound]

/-- Uniform comparison with the top of the selected semicircle on the central
sector. The straight segment stays above height `B/16`. -/
theorem central_sector_log_bound
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hzlow : B / 8 ≤ ‖z‖) (hzup : ‖z‖ ≤ B)
    (hzim : ‖z‖ / 2 ≤ z.im) :
    Real.log ‖F z - a‖ ≤ Real.log ‖F ((B : ℂ) * Complex.I) - a‖ + 4096 * Real.pi := by
  let S : Set ℂ := {w | B / 16 ≤ w.im}
  have hS : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    change B / 16 ≤ (s • x + t • y).im
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    dsimp only [S, Set.mem_ofPred_eq] at hx hy
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  have hzS : z ∈ S := by change B / 16 ≤ z.im; linarith
  have htopS : (B : ℂ) * Complex.I ∈ S := by
    change B / 16 ≤ ((B : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    linarith
  have hlog := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (log_norm_fderiv_le_of_height hF hi ha (by positivity : 0 < B / 16) hw).1)
    (fun w hw => (log_norm_fderiv_le_of_height hF hi ha (by positivity : 0 < B / 16) hw).2)
    hS htopS hzS
  have hdist : ‖z - (B : ℂ) * Complex.I‖ ≤ 2 * B := by
    calc
      ‖z - (B : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(B : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ 2 * B := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB,
          Complex.norm_I, mul_one]
        linarith
  have hnon : 0 ≤ (128 * Real.pi) / (B / 16) := by positivity
  have hconst : (128 * Real.pi) / (B / 16) * (2 * B) = 4096 * Real.pi := by
    field_simp
    ring
  have hh := hlog.trans (mul_le_mul_of_nonneg_left hdist hnon)
  rw [hconst, Real.norm_eq_abs] at hh
  linarith [le_abs_self (Real.log ‖F z - a‖ - Real.log ‖F ((B : ℂ) * Complex.I) - a‖)]

theorem central_sector_norm_bound
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hzlow : B / 8 ≤ ‖z‖) (hzup : ‖z‖ ≤ B)
    (hzim : ‖z‖ / 2 ≤ z.im) :
    ‖F z - a‖ ≤ ‖F ((B : ℂ) * Complex.I) - a‖ * Real.exp (4096 * Real.pi) := by
  have hzH : 0 < z.im := by linarith
  have htopH : 0 < ((B : ℂ) * Complex.I).im := by simpa using hB
  have hnz : 0 < ‖F z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ha z hzH))
  have hntop : 0 < ‖F ((B : ℂ) * Complex.I) - a‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (ha _ htopH))
  have hh := Real.exp_le_exp.mpr (central_sector_log_bound hF hi ha hB hzlow hzup hzim)
  simpa only [Real.exp_add, Real.exp_log hnz, Real.exp_log hntop] using hh

/-- Semicircles and their central sectors can be made arbitrarily small in
parameter space while preserving a uniform image bound. -/
theorem exists_arbitrarily_small_image_sector
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r A t₀ : ℝ} {β : ℝ → ℂ}
    (hr : 0 < r) (hA : 2 * Real.pi ^ 2 < A)
    (ht₀ : 0 < t₀) (hβ : ContinuousOn β (Icc 0 t₀)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 t₀, 0 < (β t).im)
    (hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r * Real.exp (-A)) :
    ∀ δ : ℝ, 0 < δ → ∃ B ∈ Ioo 0 δ,
      (∀ θ ∈ Ioo 0 Real.pi,
        ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ ≤
          r * Real.exp (-A + Real.pi * Real.sqrt (2 * A))) ∧
      ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
        ‖F z - a‖ ≤ r * Real.exp (-A + Real.pi * Real.sqrt (2 * A) + 4096 * Real.pi) := by
  intro δ hδ
  obtain ⟨B, hB, hcircle⟩ := exists_arbitrarily_small_image_semicircle hF hi ha hr hA
    ht₀ hβ hβ₀ hβH hsmall δ hδ
  refine ⟨B, hB, hcircle, ?_⟩
  intro z hzlow hzup hzim
  have htop := hcircle (Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I] at htop
  calc
    ‖F z - a‖ ≤ ‖F ((B : ℂ) * Complex.I) - a‖ * Real.exp (4096 * Real.pi) :=
      central_sector_norm_bound hF hi ha hB.1 hzlow hzup hzim
    _ ≤ (r * Real.exp (-A + Real.pi * Real.sqrt (2 * A))) * Real.exp (4096 * Real.pi) :=
      mul_le_mul_of_nonneg_right htop (Real.exp_pos _).le
    _ = _ := by simp only [Real.exp_add, mul_assoc]

lemma sector_exponential_lt_quarter {A : ℝ} (hA : 65536 ≤ A) :
    Real.exp (-A + Real.pi * Real.sqrt (2 * A) + 4096 * Real.pi) < 1 / 4 := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hsqrt : Real.sqrt (2 * A) ≤ A / 8 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ A by positivity) (show 0 ≤ A - 128 by linarith)]
  have hpi : Real.pi * Real.sqrt (2 * A) ≤ 4 * (A / 8) :=
    mul_le_mul Real.pi_lt_four.le hsqrt (Real.sqrt_nonneg _) (by norm_num)
  have hexp : -A + Real.pi * Real.sqrt (2 * A) + 4096 * Real.pi < -3 := by
    linarith [Real.pi_lt_four]
  have hthree : (4 : ℝ) < Real.exp 3 := by
    have hh := Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)
    norm_num only at hh
    exact hh
  calc
    _ < Real.exp (-3) := Real.exp_lt_exp.mpr hexp
    _ < 1 / 4 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) hthree

/-- A fixed sufficiently deep guide segment provides the small semicircle
and central sector used to splice the initial passage. -/
theorem exists_arbitrarily_small_quarter_image_sector
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r t₀ : ℝ} {β : ℝ → ℂ}
    (hr : 0 < r) (ht₀ : 0 < t₀) (hβ : ContinuousOn β (Icc 0 t₀)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 t₀, 0 < (β t).im)
    (hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r * Real.exp (-65536)) :
    ∀ δ : ℝ, 0 < δ → ∃ B ∈ Ioo 0 δ,
      (∀ θ ∈ Ioo 0 Real.pi,
        ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ < r / 4) ∧
      ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im → ‖F z - a‖ < r / 4 := by
  have hA : 2 * Real.pi ^ 2 < (65536 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  intro δ hδ
  obtain ⟨B, hB, hcircle, hsector⟩ := exists_arbitrarily_small_image_sector hF hi ha hr hA
    ht₀ hβ hβ₀ hβH hsmall δ hδ
  have hc := semicircle_exponential_lt_quarter (A := 65536) (by norm_num)
  have hs := sector_exponential_lt_quarter (A := 65536) (by norm_num)
  refine ⟨B, hB, ?_, ?_⟩
  · intro θ hθ
    have hle := hcircle θ hθ
    have he : Real.exp (-(65536 : ℝ) + Real.pi * Real.sqrt (2 * 65536)) < 1 / 4 :=
      (Real.exp_le_exp.mpr (by norm_num)).trans_lt hc
    exact hle.trans_lt (by simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left he hr)
  · intro z hzlow hzup hzim
    exact (hsector z hzlow hzup hzim).trans_lt
      (by simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left hs hr)

/-- Full access-guide formulation: convergence to the omitted boundary value
itself supplies the initial short segment needed above. -/
theorem access_guide_has_arbitrarily_small_quarter_image_sector
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r T : ℝ} {β : ℝ → ℂ}
    (hr : 0 < r) (hT : 0 < T) (hβ : ContinuousOn β (Icc 0 T)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hlimit : Tendsto (F ∘ β) (𝓝[>] 0) (𝓝 a)) :
    ∀ δ : ℝ, 0 < δ → ∃ B ∈ Ioo 0 δ,
      (∀ θ ∈ Ioo 0 Real.pi,
        ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ < r / 4) ∧
      ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im → ‖F z - a‖ < r / 4 := by
  have hε : 0 < r * Real.exp (-65536) := mul_pos hr (Real.exp_pos _)
  obtain ⟨d, hd, hdbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlimit _ hε
  let t₀ := min T (d / 2)
  have ht₀ : 0 < t₀ := lt_min hT (by positivity)
  have ht₀T : t₀ ≤ T := min_le_left _ _
  have hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r * Real.exp (-65536) := by
    intro t ht
    apply le_of_lt
    have htd : dist t 0 < d := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact (ht.2.trans (min_le_right _ _)).trans_lt (by linarith)
    simpa only [Function.comp_apply, dist_eq_norm] using hdbound ht.1 htd
  exact exists_arbitrarily_small_quarter_image_sector hF hi ha hr ht₀
    (hβ.mono (Icc_subset_Icc_right ht₀T)) hβ₀
    (fun t ht => hβH t ⟨ht.1, ht.2.trans ht₀T⟩) hsmall

end SLEExactGauge.SmallImageSemicircle

end

end OAI
