import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Hecke.Dyadic
import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex

namespace SevenEighths.GammaZeroDetector

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := CubicGammaExponential.real_Gamma_compact_bound
    (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := CubicGammaExponential.norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

theorem gamma_rapid_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := CubicGammaExponential.real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Gamma z‖ ≤ C₀ :=
      (CubicGammaExponential.norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza,hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem gamma_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

def cancelledKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma (z + 1) * dslope f 0 z * g z

def literalKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma z * f z * g z

theorem cancelledKernel_eq_literal {f g : ℂ → ℂ} {Y : ℝ} (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : cancelledKernel f g Y z = literalKernel f g Y z := by
  unfold cancelledKernel literalKernel
  rw [Gamma_add_one z hz, dslope_of_ne f hz]
  simp only [slope, sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

theorem cancelledKernel_at_zero (f g : ℂ → ℂ) (Y : ℝ) :
    cancelledKernel f g Y 0 = deriv f 0 * g 0 := by
  simp [cancelledKernel, Complex.cpow_zero, Complex.Gamma_one]

theorem dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hf.differentiableOn

theorem cancelledKernel_differentiableAt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {Y : ℝ} (hY : 0 < Y) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (cancelledKernel f g Y) z := by
  exact ((((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).mul
    ((gamma_differentiableAt_right (by change 0 < z.re + 1; linarith)).comp z
      (differentiableAt_id.add_const 1))).mul (dslope_entire hf z)).mul (hg z))

theorem literalKernel_norm (f g : ℂ → ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖literalKernel f g Y z‖ = Y ^ z.re * ‖Gamma z‖ * ‖f z‖ * ‖g z‖ := by
  simp only [literalKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]

theorem cancelledKernel_large_height_bound {f g : ℂ → ℂ} (hf0 : f 0 = 0)
    {Y a b A B G : ℝ} (hY : 1 ≤ Y) (_ha : -1 < a) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hG : 0 ≤ G)
    (hgamma : ∀ z : ℂ, a + 1 ≤ z.re → z.re ≤ b + 1 →
      (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzi : 1 ≤ |z.im|) :
    ‖cancelledKernel f g Y z‖ ≤ (Y ^ b * G * A * B) / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzi
  have hnorm : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hΓ : ‖Gamma z‖ ≤ ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hga := hgamma (z + 1) (by simpa using hza) (by simpa using hzb)
  simp only [add_im, one_im, add_zero] at hga
  have hweighted : (1 + z.im ^ 2) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) ≤ G := by
    calc
      _ ≤ (1 + |z.im|) ^ 2 * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by
        gcongr
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      _ = (1 + |z.im|) ^ (n + 2) * ‖Gamma (z + 1)‖ := by rw [pow_add]; ring
      _ ≤ _ := hga
  have hgdiv : ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n ≤ G / (1 + z.im ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hweighted)
  rw [cancelledKernel_eq_literal hf0 hz0, literalKernel_norm f g hY0]
  calc
    _ ≤ Y ^ b * ‖Gamma (z + 1)‖ * (A * (1 + |z.im|) ^ n) * B := by
      gcongr
      · exact hf z hza hzb
      · exact hg z hza hzb
    _ = (Y ^ b * A * B) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by ring
    _ ≤ (Y ^ b * A * B) * (G / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hgdiv (by positivity)
    _ = _ := by ring

theorem cancelledKernel_strip_bound {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨G,hG,hgamma⟩ := gamma_rapid_bound (a+1) (b+1) (by linarith) (n+2)
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hc : ContinuousOn (cancelledKernel f g Y) S := by
    intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz.1.1)).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖cancelledKernel f g Y z‖) S :=
    (continuous_const.add (continuous_im.pow 2)).continuousOn.mul hc.norm
  obtain ⟨K,hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact S).bddAbove_image hw
  refine ⟨|K| + Y ^ b * G * A * B + 1, by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · apply (cancelledKernel_large_height_bound hf0 hY ha n hA hB hG.le hgamma
      hfbound hgbound hza hzb ht).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [abs_nonneg K]
  · have hzS : z ∈ S := ⟨⟨hza,hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have hb := hK (Set.mem_image_of_mem _ hzS)
    apply (le_div_iff₀ (by positivity : 0 < 1 + z.im ^ 2)).mpr
    have hnonneg : 0 ≤ Y ^ b * G * A * B := by positivity
    nlinarith [le_abs_self K]

theorem cancelledKernel_vertical_integrable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {Y a b C x : ℝ}
    (hY : 0 < Y) (ha : -1 < a) (hx : x ∈ Icc a b)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
  have hc : Continuous (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cancelledKernel_differentiableAt hf hg hY (by simpa using ha.trans_le hx.1)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro t
  simpa [div_eq_mul_inv] using hbound ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem cancelledKernel_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (hab : a ≤ b) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    (∫ t : ℝ, cancelledKernel f g Y ((a : ℂ) + t * I)) =
      ∫ t : ℝ, cancelledKernel f g Y ((b : ℂ) + t * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C,_,hbnd⟩ := cancelledKernel_strip_bound hf hg hf0 hY ha n hA hB hfbound hgbound
  apply VerticalContourShift.integral_eq_of_strip_decay _ a b C hab
    (fun z hz _ => cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz))
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨le_rfl,hab⟩ hbnd)
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨hab,le_rfl⟩ hbnd)
  intro x hx t
  simpa using hbnd ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem literal_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y A B : ℝ}
    (hY : 1 ≤ Y) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) :
    (∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I) := by
  have h := cancelledKernel_contour_shift hf hg hf0 hY (by norm_num : (-1 : ℝ) < -(1/4))
    (by norm_num : (-(1/4) : ℝ)≤2) n hA hB hfbound hgbound
  have he (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      cancelledKernel f g Y ((x : ℂ) + t * I) = literalKernel f g Y ((x : ℂ) + t * I) := by
    apply cancelledKernel_eq_literal hf0
    intro hz
    apply hx
    simpa using congrArg Complex.re hz
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h
  have h2 (t : ℝ) := he 2 (by norm_num) t
  have hq (t : ℝ) := he (-(1/4)) (by norm_num) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h2 hq
  simpa only [h2, hq] using h.symm

theorem gamma_negative_quarter_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ,
      (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G := by
  obtain ⟨C,hC,hgamma⟩ := gamma_rapid_bound (3/4) (3/4) (by norm_num) (n+2)
  refine ⟨4*C, by positivity, ?_⟩
  intro t
  let z : ℂ := (-(1/4) : ℂ) + t * I
  have hzre : z.re = -(1/4) := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzre
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by simpa only [hzre, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<1/4)] using Complex.abs_re_le_norm z
  have hΓ : ‖Gamma z‖ ≤ 4 * ‖Gamma (z+1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    nlinarith [norm_nonneg (Gamma z)]
  have hbound := hgamma (z+1) (by norm_num [hzre]) (by norm_num [hzre])
  simp only [add_im, one_im, add_zero, hzim] at hbound
  have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
  change (1+t^2)*(1+|t|)^n*‖Gamma z‖ ≤ 4*C
  calc
    _ ≤ (1+|t|)^2*(1+|t|)^n*(4*‖Gamma (z+1)‖) := by gcongr
    _ = 4*((1+|t|)^(n+2)*‖Gamma (z+1)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem literal_shifted_integral_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      0 < Y → 0 ≤ A → 0 ≤ B →
      (∀ t : ℝ, ‖f ((-(1/4) : ℂ)+t*I)‖ ≤ A*(1+|t|)^n) →
      (∀ t : ℝ, ‖g ((-(1/4) : ℂ)+t*I)‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hgamma⟩ := gamma_negative_quarter_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hY hA hB hf hg
  have hbound (t : ℝ) :
      ‖literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        (G*A*B*Y^(-(1/4 : ℝ)))*(1+t^2)⁻¹ := by
    have hga : (1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖ ≤ G/(1+t^2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hgamma t])
    rw [literalKernel_norm f g hY]
    have hzre : (((-(1/4) : ℂ)+t*I).re) = (-(1/4) : ℝ) := by norm_num
    rw [hzre]
    change Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*
      ‖f ((-(1/4) : ℂ)+t*I)‖*‖g ((-(1/4) : ℂ)+t*I)‖ ≤ _
    calc
      _ ≤ Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*(A*(1+|t|)^n)*B := by gcongr; exact hf t; exact hg t
      _ = (A*B*Y^(-(1/4 : ℝ)))*((1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖) := by ring
      _ ≤ (A*B*Y^(-(1/4 : ℝ)))*(G/(1+t^2)) := mul_le_mul_of_nonneg_left hga (by positivity)
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (G*A*B*Y^(-(1/4 : ℝ)))) (ae_of_all _ hbound)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  convert hint using 1; ring

theorem literal_detector_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      Differentiable ℂ f → Differentiable ℂ g → f 0 = 0 →
      1 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A*(1+|z.im|)^n) →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hbound⟩ := literal_shifted_integral_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hf hg hf0 hY hA hB hfb hgb
  rw [literal_contour_shift hf hg hf0 hY n hA hB hfb hgb]
  apply hbound f g Y A B (by linarith) hA hB
  · intro t; simpa using hfb ((-(1/4) : ℂ)+t*I) (by norm_num) (by norm_num)
  · intro t; exact hgb _ (by norm_num) (by norm_num)

open HeckeFamily

def cutoffSet (D : ℝ) : Finset (Ideal O) :=
  ConcretePrimeRowBridge.idealsUpTo ⌊2*D⌋₊

theorem mem_cutoffSet {D : ℝ} (hD : 0 ≤ D) {J : Ideal O} :
    J ∈ cutoffSet D ↔ J ≠ 0 ∧ (J.absNorm : ℝ) ≤ 2*D := by
  rw [cutoffSet, ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨?_, ?_⟩
    · intro h; simp [h] at hp
    · exact (by exact_mod_cast hb : (J.absNorm : ℝ) ≤ ⌊2*D⌋₊).trans
        (Nat.floor_le (by positivity))
  · rintro ⟨hp, hb⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp),
      Nat.le_floor hb⟩

def cutoffTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) : ℂ :=
  HeckeDyadic.coefficient χ true J * V ((J.absNorm : ℝ)/D) *
    CubicEisenstein.fullIdealWeight s J

def cutoff (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  ∑ J ∈ cutoffSet D, cutoffTerm χ V D J s

@[simp] theorem cutoffTerm_zero (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) :
    cutoffTerm χ V D 0 s = 0 := by
  simp [cutoffTerm, CubicEisenstein.fullIdealWeight]

theorem cutoffTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) {J : Ideal O}
    (hJ : J ≠ 0) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      idealCoeff χ J * V ((J.absNorm : ℝ)/D) * (J.absNorm : ℂ)^(-s) := by
  rw [cutoffTerm, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
  rfl

theorem cutoff_eq_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    cutoff χ V D s = ∑' J : Ideal O, cutoffTerm χ V D J s := by
  symm
  apply tsum_eq_sum
  intro J hJ
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) :
    Differentiable ℂ (cutoffTerm χ V D J) := by
  by_cases hJ : J = 0
  · subst J
    have he : cutoffTerm χ V D 0 = fun _ : ℂ => 0 := funext (cutoffTerm_zero χ V D)
    rw [he]
    exact differentiable_const 0
  · have hn : (J.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
    unfold cutoffTerm
    simp only [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
    exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem cutoff_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (cutoff χ V D) := by
  exact Differentiable.fun_sum fun J _ => cutoffTerm_entire χ V D J

theorem cutoffTerm_norm_le (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) (J : Ideal O) :
    ‖cutoffTerm χ V D J s‖ ≤ 1 := by
  by_cases hJ : J = 0
  · subst J
    rw [cutoffTerm_zero, norm_zero]
    norm_num
  · have hnorm : 1 ≤ (J.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
    have hw : ‖CubicEisenstein.fullIdealWeight s J‖ ≤ 1 := by
      rw [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
      have hn : 0 < (J.absNorm : ℝ) := by linarith
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, neg_re]
      exact (Real.rpow_le_rpow_of_exponent_le hnorm (neg_nonpos.mpr hs)).trans_eq (Real.rpow_zero _)
    rw [cutoffTerm, norm_mul, norm_mul]
    calc
      _ ≤ (1 : ℝ)*1*1 := by gcongr; exact HeckeDyadic.coefficient_norm_le χ true J; exact hV _
      _ = 1 := by norm_num

theorem cutoff_norm_le (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 1 ≤ D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cutoff χ V D s‖ ≤ 256*D := by
  have hcount := DescentFiberCost.finite_ideal_count_real (cutoffSet D) (2*D) (by linarith)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).1)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).2)
  calc
    _ ≤ ∑ J ∈ cutoffSet D, ‖cutoffTerm χ V D J s‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ cutoffSet D, (1 : ℝ) := Finset.sum_le_sum (fun J _ => cutoffTerm_norm_le χ V D hV hs J)
    _ = ((cutoffSet D).card : ℝ) := by simp
    _ ≤ 256*D := by linarith

theorem original_right_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ s : ℂ,
      (1/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤
        C*(χ.modulus.absNorm : ℝ)^2*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound
    (1/4) 1 (by norm_num) (by norm_num)
  let Cp := HeckeLogarithmicInput.uniformConstant
  have hCp : 0 ≤ Cp := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨(1+Cp)*Cd, by positivity, ?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ
    ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hL := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ) ≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hL
  have hnorm : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
  have hqp : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ χ.modulus.absNorm := by
    apply le_trans _ hnorm
    simpa using Real.rpow_le_rpow_of_exponent_le
      (HeckeLogarithmicInput.modulus_norm_ge_one ψ) (by norm_num : (3/5 : ℝ) ≤ 1)
  have hLd : ‖LFunction ψ s‖ ≤ (1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2 := by
    apply hL.trans
    change Cp * _ * _ ≤ _
    gcongr
    linarith
  have hd := hdel χ.modulus χ.modulus_ne_bot ψ s hs
  rw [Real.rpow_one] at hd
  have hd' : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖ ≤ Cd*(χ.modulus.absNorm : ℝ) := by
    linarith [norm_nonneg ((HeckeFiniteDeletion.factors χ.modulus ψ s)⁻¹)]
  rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith), norm_mul]
  calc
    _ ≤ ((1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2) *
        (Cd*(χ.modulus.absNorm : ℝ)) := mul_le_mul hLd hd' (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem shifted_original_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ (ρ z : ℂ),
      (51/100 : ℝ) ≤ ρ.re → -(1/4 : ℝ) ≤ z.re →
      ‖LFunction χ (ρ+z)‖ ≤
        (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2)*(1+|z.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := original_right_growth
  refine ⟨C,hC,?_⟩
  intro χ hχ ρ z hρ hz
  have hb := hbound χ hχ (ρ+z) (by simp only [add_re]; linarith)
  have hh : 3+|(ρ+z).im| ≤ (3+|ρ.im|)*(1+|z.im|) := by
    simp only [add_im]
    have hab := abs_add_le ρ.im z.im
    nlinarith [abs_nonneg ρ.im, abs_nonneg z.im]
  calc
    _ ≤ C*(χ.modulus.absNorm : ℝ)^2*((3+|ρ.im|)*(1+|z.im|))^2 := by
      apply hb.trans; gcongr
    _ = _ := by ring

def detectorIntegrand (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ z : ℂ) : ℂ :=
  (Y : ℂ)^z * Gamma z * LFunction χ (ρ+z) * cutoff χ V D (ρ+z)

def detectorIntegral (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ : ℂ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)

theorem detector_contour_shift (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) :
    (∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) =
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (-(1/4)+t*I) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  apply literal_contour_shift (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY 2 (by positivity) (by positivity : 0 ≤ 256*D)
  · intro z hz _
    exact hgrowth χ hχ ρ z hρ hz
  · intro z hz _
    exact cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith)

theorem detector_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : Character), χ.residue ≠ 1 →
      ∀ (V : ℝ → ℂ), (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (D Y : ℝ),
      1 ≤ D → 1 ≤ Y → ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 →
      ‖detectorIntegral χ V D Y ρ‖ ≤
        K*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2*D*Y^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  obtain ⟨G,hG,hgamma⟩ := literal_detector_bound 2
  refine ⟨128*G*C, by positivity, ?_⟩
  intro χ hχ V hV D Y hD hY ρ hρ hzero
  have hb := hgamma (fun z => LFunction χ (ρ+z)) (fun z => cutoff χ V D (ρ+z))
    Y (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (by simp only [add_re]; linarith))
  change ‖∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)‖ ≤ _ at hb
  rw [detectorIntegral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp
  ring

theorem detector_integrable (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) {x : ℝ} (hx : x ∈ Icc (-(1/4)) 2) (hx0 : x ≠ 0) :
    Integrable (fun t : ℝ => detectorIntegrand χ V D Y ρ ((x : ℂ)+t*I)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  let f : ℂ → ℂ := fun z => LFunction χ (ρ+z)
  let g : ℂ → ℂ := fun z => cutoff χ V D (ρ+z)
  have hf : Differentiable ℂ f :=
    (LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id)
  have hg : Differentiable ℂ g :=
    (cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id)
  have hf0 : f 0 = 0 := by simpa [f] using hzero
  obtain ⟨B,_,hb⟩ := cancelledKernel_strip_bound (b := 2) hf hg hf0 hY
    (by norm_num : (-1 : ℝ) < -(1/4)) 2
    (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith))
  have hi := cancelledKernel_vertical_integrable hf hg (by linarith : 0 < Y)
    (by norm_num : (-1 : ℝ) < -(1/4)) hx hb
  apply hi.congr
  filter_upwards [] with t
  apply cancelledKernel_eq_literal hf0
  intro hz
  apply hx0
  simpa using congrArg Complex.re hz

theorem detectorIntegral_contour_normalization (χ : Character) (V : ℝ → ℂ)
    (D Y : ℝ) (ρ : ℂ) :
    detectorIntegral χ V D Y ρ = ((2*Real.pi : ℂ)*I)⁻¹ *
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)*I := by
  rw [MeasureTheory.integral_mul_const, mul_inv_rev]
  simp only [detectorIntegral, ofReal_mul, ofReal_ofNat]
  have hi : I⁻¹*I = 1 := inv_mul_cancel₀ I_ne_zero
  calc
    _ = (I⁻¹*I)*(((2*Real.pi : ℂ))⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) := by rw [hi, one_mul]
    _ = _ := by ring

theorem detector_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (R θ : ℝ), 0 ≤ R → 0 ≤ θ →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (U D : ℝ), 1 ≤ U →
      1 ≤ D → D ≤ U^(3/2 : ℝ) → (χ.modulus.absNorm : ℝ) ≤ R*U →
      ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ ≤ (K*R^2)*U^(-(3/2 : ℝ)+2*θ) := by
  obtain ⟨K,hK,hbound⟩ := detector_integral_bound
  refine ⟨16*K, by positivity, ?_⟩
  intro R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht
  have hU0 : 0 < U := by linarith
  have huθ : 1 ≤ U^θ := Real.one_le_rpow hU hθ
  have hheight : 3+|ρ.im| ≤ 4*U^θ := by linarith
  have hY : 1 ≤ U^20 := one_le_pow₀ hU
  have he : (U^20)^(-(1/4 : ℝ)) = U^(-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hb := hbound χ hχ V hV D (U^20) hD hY ρ hρ hzero
  rw [he] at hb
  calc
    _ ≤ K*(R*U)^2*(4*U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ) := by
      apply hb.trans; gcongr
    _ = (16*K*R^2)*(U^(2 : ℝ)*(U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hU0.le, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 2
      ring

theorem detector_uniform_small (R θ ε : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ D : ℝ, 1 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ < ε := by
  obtain ⟨K,hK,hbound⟩ := detector_power_bound
  have ht : Tendsto (fun U : ℝ => (K*R^2)*U^(-(3/2 : ℝ)+2*θ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (3/2 : ℝ)-2*θ)).const_mul (K*R^2)
    simpa [neg_sub, sub_eq_add_neg, add_comm] using h
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ hχ V hV D hD hDU hQ ρ hρ hzero ht
  exact (hbound R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht).trans_lt (hU₀ U hU₀')

end SevenEighths.GammaZeroDetector

end

end OAI
