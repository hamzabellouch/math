import Mathlib

namespace OAI

/-! Positive Fourier laws, compact integral differentiation, affine densities, and prime-sieve signal laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

/-! The positive Fourier law. The sinc and averaged
baseline below are exactly those of the manuscript, including the scale and
normalization. -/
open scoped FourierTransform Convolution

lemma sinc_eq_integral_cos (x : ℝ) :
    Real.sinc x = ∫ t in (0 : ℝ)..1, Real.cos (x*t) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [intervalIntegral.integral_comp_mul_left _ hx,integral_cos]
    simp only [mul_zero,mul_one,Real.sin_zero,sub_zero,smul_eq_mul]
    rw [Real.sinc_of_ne_zero hx]
    ring

lemma smooth_sinc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.sinc := by
  rw [show Real.sinc = (fun x => ∫ t in (0 : ℝ)..1, Real.cos (x*t)) from
    funext sinc_eq_integral_cos]
  exact smooth_compact_integral (F := fun p : ℝ × ℝ => Real.cos (p.1*p.2)) (by fun_prop) 0 1

def signalSinc (α R : ℝ) : ℝ := α * Real.sinc (Real.pi*α*R)^2

def signalAverageRadius (α : ℝ) : ℝ := (2*α)⁻¹

def signalBaseline (α R : ℝ) : ℝ :=
  (2*signalAverageRadius α)⁻¹ *
    ∫ t in -signalAverageRadius α..signalAverageRadius α, signalSinc α (R-t)

lemma signalSinc_nonneg {α : ℝ} (hα : 0 ≤ α) (R : ℝ) : 0 ≤ signalSinc α R :=
  mul_nonneg hα (sq_nonneg _)

lemma smooth_signalSinc (α : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalSinc α) := by
  exact contDiff_const.mul ((smooth_sinc.comp (by fun_prop)).pow 2)

lemma smooth_signalBaseline (α : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalBaseline α) := by
  apply contDiff_const.mul
  exact smooth_compact_integral (F := fun p : ℝ × ℝ => signalSinc α (p.1-p.2))
    ((smooth_signalSinc α).comp (by fun_prop)) _ _

lemma sinc_sq_le (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg (Real.sinc x)) (by norm_num : (0:ℝ) ≤ 1)).2 (Real.abs_sinc_le_one x)

lemma sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg (Real.sin x)) (by norm_num : (0:ℝ) ≤ 1)).2 (Real.abs_sin_le_one x)

lemma sinc_sq_mul_sq_le (x : ℝ) : Real.sinc x ^ 2 * x^2 ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp
    exact sin_sq_le_one x

lemma signalSinc_decay {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalSinc α R ≤ (α + (Real.pi^2*α)⁻¹) * (1+R^2)⁻¹ := by
  have ha : Real.pi^2*α > 0 := by positivity
  have hsmall : signalSinc α R ≤ α :=
    mul_le_of_le_one_right hα.le (sinc_sq_le _)
  have hlarge : signalSinc α R * R^2 ≤ (Real.pi^2*α)⁻¹ := by
    have := sinc_sq_mul_sq_le (Real.pi*α*R)
    rw [← one_div]
    apply (le_div_iff₀ ha).2
    dsimp [signalSinc]
    nlinarith
  have hd : 0 < 1+R^2 := by positivity
  rw [← div_eq_mul_inv,le_div_iff₀ hd]
  nlinarith

lemma integrable_signalSinc {α : ℝ} (hα : 0 < α) : Integrable (signalSinc α) := by
  apply (integrable_inv_one_add_sq.const_mul (α + (Real.pi^2*α)⁻¹)).mono'
    (smooth_signalSinc α).continuous.aestronglyMeasurable
  filter_upwards [] with R
  rw [Real.norm_eq_abs,abs_of_nonneg (signalSinc_nonneg hα.le R)]
  exact signalSinc_decay hα R

lemma signalAverageRadius_pos {α : ℝ} (hα : 0 < α) : 0 < signalAverageRadius α := by
  dsimp [signalAverageRadius]
  positivity

lemma signalSinc_denominator {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalSinc α R * (Real.pi^2*α*R^2) = Real.sin (Real.pi*α*R)^2 := by
  by_cases hR : R = 0
  · simp [hR]
  · dsimp [signalSinc]
    rw [Real.sinc_of_ne_zero (by positivity : Real.pi*α*R ≠ 0)]
    field_simp

lemma integral_sin_sq_pi (x : ℝ) :
    ∫ t in x..x+Real.pi, Real.sin t^2 = Real.pi/2 := by
  rw [integral_sin_sq,Real.sin_add_pi,Real.cos_add_pi]
  ring

lemma signal_sin_sq_average {α : ℝ} (hα : 0 < α) (R : ℝ) :
    ∫ t in -signalAverageRadius α..signalAverageRadius α,
      Real.sin (Real.pi*α*(R-t))^2 = signalAverageRadius α := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => Real.sin (Real.pi*α*u)^2) R]
  rw [intervalIntegral.integral_comp_mul_left (fun v => Real.sin v^2)
    (mul_ne_zero Real.pi_ne_zero hα.ne')]
  have hh : Real.pi*α*(R- -signalAverageRadius α) =
      Real.pi*α*(R-signalAverageRadius α)+Real.pi := by
    dsimp [signalAverageRadius]
    field_simp
    ring
  rw [hh,integral_sin_sq_pi,smul_eq_mul]
  dsimp [signalAverageRadius]
  field_simp

lemma signalBaseline_nonneg {α : ℝ} (hα : 0 < α) (R : ℝ) :
    0 ≤ signalBaseline α R := by
  apply mul_nonneg (by dsimp [signalAverageRadius]; positivity)
  apply intervalIntegral.integral_nonneg (by linarith [signalAverageRadius_pos hα])
  intro t _
  exact signalSinc_nonneg hα.le (R-t)

/-- The averaging interval has exactly one sine-square period.  In fact the
manuscript's lower tail estimate holds at every point, including the origin. -/
lemma signalBaseline_lower {α : ℝ} (hα : 0 < α) (R : ℝ) :
    1 / (2*Real.pi^2*α*(|R|+signalAverageRadius α)^2) ≤ signalBaseline α R := by
  let a := signalAverageRadius α
  have ha : 0 < a := signalAverageRadius_pos hα
  have hκ : 0 < Real.pi^2*α*(|R|+a)^2 := by positivity
  have hp : 0 < Real.pi^2*α := by positivity
  have hi :
      a ≤ (Real.pi^2*α*(|R|+a)^2) * ∫ t in -a..a, signalSinc α (R-t) := by
    calc
      a = ∫ t in -a..a, Real.sin (Real.pi*α*(R-t))^2 := (signal_sin_sq_average hα R).symm
      _ ≤ _ := ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous (fun t => Real.sin (Real.pi*α*(R-t))^2)).intervalIntegrable _ _)
      (by exact (continuous_const.mul
        ((smooth_signalSinc α).continuous.comp (by fun_prop))).intervalIntegrable _ _)
    intro t ht
    have ht' : |t| ≤ a := abs_le.mpr ⟨ht.1,ht.2⟩
    have hdist : |R-t| ≤ |R|+a := (abs_sub R t).trans (by linarith)
    have hs : (R-t)^2 ≤ (|R|+a)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdist
    rw [← signalSinc_denominator hα (R-t)]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hp.le)
      (signalSinc_nonneg hα.le (R-t))]
  rw [div_le_iff₀ (by positivity : 0 < 2*Real.pi^2*α*(|R|+signalAverageRadius α)^2)]
  dsimp [signalBaseline]
  change 1 ≤ ((2*a)⁻¹ * ∫ t in -a..a, signalSinc α (R-t)) *
    (2*Real.pi^2*α*(|R|+a)^2)
  field_simp
  nlinarith

lemma shifted_quadratic_bound {a R t : ℝ} (ha : 0 ≤ a) (ht : |t| ≤ a) :
    1+R^2 ≤ 2*(1+a^2)*(1+(R-t)^2) := by
  have ht2 : t^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).2 ht
  nlinarith [sq_nonneg (R-2*t),mul_nonneg (sq_nonneg a) (sq_nonneg (R-t))]

lemma signalBaseline_upper {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalBaseline α R ≤
      (α+(Real.pi^2*α)⁻¹)* (2*(1+(signalAverageRadius α)^2))* (1+R^2)⁻¹ := by
  let a := signalAverageRadius α
  let C := α+(Real.pi^2*α)⁻¹
  have ha : 0 < a := signalAverageRadius_pos hα
  have hC : 0 < C := by dsimp [C]; positivity
  have hi : (∫ t in -a..a, signalSinc α (R-t)) ≤
      (2*a) * (C * (2*(1+a^2))* (1+R^2)⁻¹) := by
    calc
      _ ≤ ∫ _t in -a..a, C * (2*(1+a^2))* (1+R^2)⁻¹ := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (((smooth_signalSinc α).continuous.comp (by fun_prop)).intervalIntegrable _ _)
          intervalIntegrable_const
        intro t ht
        have hs := shifted_quadratic_bound (R := R) ha.le (abs_le.mpr ⟨ht.1,ht.2⟩)
        have hd : 0 < 1+(R-t)^2 := by positivity
        have hD : 0 < 1+R^2 := by positivity
        calc
          signalSinc α (R-t) ≤ C*(1+(R-t)^2)⁻¹ := signalSinc_decay hα (R-t)
          _ ≤ C*(2*(1+a^2))*(1+R^2)⁻¹ := by
            rw [← div_eq_mul_inv,← div_eq_mul_inv]
            apply (div_le_div_iff₀ hd hD).2
            nlinarith
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  dsimp [signalBaseline]
  change (2*a)⁻¹ * _ ≤ C*(2*(1+a^2))*(1+R^2)⁻¹
  rw [inv_mul_le_iff₀ (by positivity : 0 < 2*a)]
  exact hi

lemma integrable_signalBaseline {α : ℝ} (hα : 0 < α) : Integrable (signalBaseline α) := by
  apply (integrable_inv_one_add_sq.const_mul
    ((α+(Real.pi^2*α)⁻¹)*(2*(1+(signalAverageRadius α)^2)))).mono'
    (smooth_signalBaseline α).continuous.aestronglyMeasurable
  filter_upwards [] with R
  rw [Real.norm_eq_abs,abs_of_nonneg (signalBaseline_nonneg hα R)]
  exact signalBaseline_upper hα R

/-! Exact Fourier support, without assuming an interval inversion formula. -/
def signalBox (α : ℝ) (x : ℝ) : ℂ := (Icc (-α/2) (α/2)).indicator (fun _ => 1) x

def signalTriangle (α v : ℝ) : ℂ := ((max (α-|v|) 0 / α : ℝ) : ℂ)

lemma integrable_signalBox (α : ℝ) : Integrable (signalBox α) := by
  exact (integrableOn_const (isCompact_Icc.measure_ne_top) :
    IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-α/2) (α/2))).integrable_indicator measurableSet_Icc

lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    𝓕 (fun x => c*f x) v = c*𝓕 f v := by
  simp only [Real.fourier_real_eq,Circle.smul_def,smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

lemma fourier_signalBox {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (signalBox α) v = (α * Real.sinc (Real.pi*α*v) : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have heq : (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)*signalBox α x) =
      (Icc (-α/2) (α/2)).indicator (fun x => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)) := by
    funext x
    by_cases hx : x ∈ Icc (-α/2) (α/2) <;> simp [signalBox,Set.indicator,hx]
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -α/2 ≤ α/2)]
  by_cases hv : v = 0
  · simp [hv,intervalIntegral.integral_const]
    ring
  · let c : ℝ := -2*Real.pi*v
    have hc : c ≠ 0 := by dsimp [c]; positivity
    have he : (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)) =
        (fun x => Complex.exp (↑(c*x)*Complex.I)) := by
      funext x
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [he,intervalIntegral.integral_comp_mul_left (fun x => Complex.exp (↑x*Complex.I)) hc]
    rw [show c*(-α/2) = -(c*(α/2)) by ring,integral_exp_mul_I_eq_sinc]
    rw [show c*(α/2) = -(Real.pi*α*v) by dsimp [c]; ring,Real.sinc_neg]
    dsimp [c]
    simp only [Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
    field_simp [hvC]

lemma signalBox_convolution {α : ℝ} (_hα : 0 < α) (v : ℝ) :
    (signalBox α ⋆[ContinuousLinearMap.mul ℂ ℂ] signalBox α) v =
      (max (α-|v|) 0 : ℝ) := by
  rw [convolution_def]
  change (∫ t : ℝ, signalBox α t * signalBox α (v-t)) = _
  let l := max (-α/2) (v-α/2)
  let u := min (α/2) (v+α/2)
  have heq : (fun t => signalBox α t * signalBox α (v-t)) =
      (Icc l u).indicator (fun _ : ℝ => (1 : ℂ)) := by
    funext t
    have hm : t ∈ Icc l u ↔ t ∈ Icc (-α/2) (α/2) ∧ v-t ∈ Icc (-α/2) (α/2) := by
      dsimp [l,u]
      simp only [mem_Icc,max_le_iff,le_min_iff]
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩
        exact ⟨⟨h1,h3⟩,by constructor <;> linarith⟩
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩
        exact ⟨⟨h1,by linarith⟩,h2,by linarith⟩
    by_cases h₁ : t ∈ Icc (-α/2) (α/2) <;>
      by_cases h₂ : v-t ∈ Icc (-α/2) (α/2) <;>
      simp [signalBox,Set.indicator,hm,h₁,h₂]
  rw [heq,integral_indicator measurableSet_Icc,setIntegral_const,Real.volume_real_Icc]
  simp only [Complex.real_smul,mul_one]
  congr 1
  dsimp [l,u]
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv,min_eq_left (by linarith),show max (-α/2) (v-α/2) = v-α/2 from max_eq_right (by linarith)]
    congr 1
    ring
  · rw [abs_of_nonpos (le_of_not_ge hv),min_eq_right (by linarith),show max (-α/2) (v-α/2) = -α/2 from max_eq_left (by linarith)]
    congr 1
    ring

lemma signalTriangle_eq_convolution {α : ℝ} (hα : 0 < α) :
    signalTriangle α = fun v => (α : ℂ)⁻¹ *
      (signalBox α ⋆[ContinuousLinearMap.mul ℂ ℂ] signalBox α) v := by
  funext v
  rw [signalBox_convolution hα]
  simp [signalTriangle,div_eq_mul_inv,mul_comm]

lemma integrable_signalTriangle {α : ℝ} (hα : 0 < α) : Integrable (signalTriangle α) := by
  rw [signalTriangle_eq_convolution hα]
  exact ((integrable_signalBox α).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_signalBox α)).const_mul _

lemma continuous_signalTriangle (α : ℝ) : Continuous (signalTriangle α) := by
  fun_prop [signalTriangle]

lemma fourier_signalTriangle {α : ℝ} (hα : 0 < α) (R : ℝ) :
    𝓕 (signalTriangle α) R = (signalSinc α R : ℝ) := by
  rw [signalTriangle_eq_convolution hα,fourier_const_mul,
    Real.fourier_mul_convolution_eq (integrable_signalBox α) (integrable_signalBox α),
    fourier_signalBox hα]
  dsimp [signalSinc]
  push_cast
  field_simp

lemma fourierInv_signalSinc {α : ℝ} (hα : 0 < α) :
    𝓕⁻ (fun R => (signalSinc α R : ℂ)) = signalTriangle α := by
  have heq : 𝓕 (signalTriangle α) = (fun R => (signalSinc α R : ℂ)) :=
    funext (fourier_signalTriangle hα)
  rw [← heq]
  exact (continuous_signalTriangle α).fourierInv_fourier_eq (integrable_signalTriangle hα)
    (by rw [heq]; exact (integrable_signalSinc hα).ofReal)

lemma fourier_signalSinc {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (fun R => (signalSinc α R : ℂ)) v = signalTriangle α v := by
  have h := congrFun (fourierInv_signalSinc hα) (-v)
  rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
  simpa only [signalTriangle,abs_neg] using h

lemma signalBaseline_eq_convolution {α : ℝ} (hα : 0 < α) :
    (fun R => (signalBaseline α R : ℂ)) = fun R => ((2*signalAverageRadius α : ℝ) : ℂ)⁻¹ *
      (signalBox (2*signalAverageRadius α) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x => (signalSinc α x : ℂ))) R := by
  funext R
  have ha : 0 < signalAverageRadius α := signalAverageRadius_pos hα
  rw [convolution_def]
  change ↑(signalBaseline α R) = _ * ∫ t, signalBox (2*signalAverageRadius α) t * ↑(signalSinc α (R-t))
  have heq : (fun t => signalBox (2*signalAverageRadius α) t * (signalSinc α (R-t) : ℂ)) =
      (Icc (-signalAverageRadius α) (signalAverageRadius α)).indicator
        (fun t => (signalSinc α (R-t) : ℂ)) := by
    funext t
    have hl : -(2*signalAverageRadius α)/2 = -signalAverageRadius α := by ring
    have hu : 2*signalAverageRadius α/2 = signalAverageRadius α := by ring
    by_cases ht : t ∈ Icc (-signalAverageRadius α) (signalAverageRadius α) <;>
      simp [signalBox,hl,hu,Set.indicator,ht]
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -signalAverageRadius α ≤ signalAverageRadius α),
    intervalIntegral.integral_ofReal]
  simp only [signalBaseline,Complex.ofReal_mul,Complex.ofReal_inv]

lemma fourier_signalBaseline {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (fun R => (signalBaseline α R : ℂ)) v =
      (Real.sinc (Real.pi*(2*signalAverageRadius α)*v) : ℂ)*signalTriangle α v := by
  rw [signalBaseline_eq_convolution hα,fourier_const_mul]
  have hc := Real.fourier_mul_convolution_eq
    (integrable_signalBox (2*signalAverageRadius α)) (integrable_signalSinc hα).ofReal v
  change 𝓕 (signalBox (2*signalAverageRadius α) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun x => (signalSinc α x : ℂ))) v = _ at hc
  rw [hc,fourier_signalBox (mul_pos (by norm_num) (signalAverageRadius_pos hα)) v]
  have hs := fourier_signalSinc hα v
  change 𝓕 (fun x => (signalSinc α x : ℂ)) v = signalTriangle α v at hs
  erw [hs]
  have ha : (2*signalAverageRadius α : ℝ) ≠ 0 := (mul_pos (by norm_num) (signalAverageRadius_pos hα)).ne'
  have haC : ((2*signalAverageRadius α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have ha0 : (signalAverageRadius α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (signalAverageRadius_pos hα).ne'
  push_cast
  field_simp [ha0]

lemma integral_signalBaseline {α : ℝ} (hα : 0 < α) : ∫ R, signalBaseline α R = 1 := by
  have h := fourier_signalBaseline hα 0
  simp [Real.fourier_real_eq,signalTriangle,max_eq_left hα.le,hα.ne'] at h
  apply Complex.ofReal_injective
  calc
    ((∫ R, signalBaseline α R : ℝ) : ℂ) = ∫ R, (signalBaseline α R : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = (1 : ℂ) := h
    _ = ((1 : ℝ) : ℂ) := rfl

lemma signalBaseline_fourier_support {α v : ℝ} (hα : 0 < α) (hv : α ≤ |v|) :
    𝓕 (fun R => (signalBaseline α R : ℂ)) v = 0 := by
  rw [fourier_signalBaseline hα]
  simp [signalTriangle,max_eq_right (sub_nonpos.mpr hv)]

lemma signalBaseline_pos {α : ℝ} (hα : 0 < α) (R : ℝ) : 0 < signalBaseline α R := by
  have ha := signalAverageRadius_pos hα
  exact lt_of_lt_of_le (by positivity) (signalBaseline_lower hα R)

theorem signalBaseline_quadratic_tails {α : ℝ} (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ,
      c/(1+R^2) ≤ signalBaseline α R ∧ signalBaseline α R ≤ C/(1+R^2) := by
  let a := signalAverageRadius α
  have ha : 0 < a := signalAverageRadius_pos hα
  let c := (4*Real.pi^2*α*(1+a^2))⁻¹
  let C := (α+(Real.pi^2*α)⁻¹)*(2*(1+a^2))
  refine ⟨c,C,by dsimp [c]; positivity,by dsimp [C]; positivity,fun R => ⟨?_,?_⟩⟩
  · apply le_trans ?_ (signalBaseline_lower hα R)
    change c/(1+R^2) ≤ 1/(2*Real.pi^2*α*(|R|+a)^2)
    have hD : 0 < 2*Real.pi^2*α*(|R|+a)^2 := by positivity
    have hbig : (|R|+a)^2 ≤ 2*(1+a^2)*(1+R^2) := by
      nlinarith [sq_nonneg (|R|-a),sq_abs R,mul_nonneg (sq_nonneg a) (sq_nonneg R)]
    have hp : 0 < 2*Real.pi^2*α := by positivity
    dsimp [c]
    rw [← one_div,div_div]
    apply one_div_le_one_div_of_le hD
    nlinarith [mul_le_mul_of_nonneg_left hbig hp.le]
  · exact (signalBaseline_upper hα R).trans_eq (by dsimp [C,a]; rw [div_eq_mul_inv])

open scoped ComplexConjugate

lemma fourier_hermitian_real (d : ℝ → ℂ) (hd : ∀ v, d (-v) = conj (d v)) (R : ℝ) :
    conj (𝓕 d R) = 𝓕 d R := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_conj]
  calc
    (∫ v : ℝ, conj (Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v)) =
        ∫ v : ℝ, Complex.exp (↑(-2*Real.pi*(-v)*R)*Complex.I)*d (-v) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [map_mul,← Complex.exp_conj,hd]
      congr 2
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring
    _ = ∫ v : ℝ, Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v :=
      integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v) volume

def signalInverse (d : ℝ → ℂ) (R : ℝ) : ℝ := (𝓕 d R).re

lemma signalInverse_complex {d : ℝ → ℂ} (hd : ∀ v, d (-v) = conj (d v)) (R : ℝ) :
    (signalInverse d R : ℂ) = 𝓕 d R :=
  Complex.conj_eq_iff_re.mp (fourier_hermitian_real d hd R)

lemma signalInverse_contDiff {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalInverse d) := by
  let f := hc.toSchwartzMap hd
  exact Complex.reCLM.contDiff.comp ((𝓕 f).smooth ⊤)

lemma signalInverse_integrable {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : Integrable (signalInverse d) := by
  let f := hc.toSchwartzMap hd
  exact Complex.reCLM.integrable_comp (𝓕 f).integrable

lemma signalInverse_inversion {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hreal : ∀ v, d (-v) = conj (d v)) :
    𝓕⁻ (fun R => (signalInverse d R : ℂ)) = d := by
  have heq : (fun R => (signalInverse d R : ℂ)) = 𝓕 d :=
    funext (signalInverse_complex hreal)
  rw [heq]
  let f := hc.toSchwartzMap hd
  exact hd.continuous.fourierInv_fourier_eq (f.integrable) (𝓕 f).integrable

lemma integral_signalInverse {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hreal : ∀ v, d (-v) = conj (d v)) (h0 : d 0 = 0) :
    ∫ R, signalInverse d R = 0 := by
  have h := congrFun (signalInverse_inversion hd hc hreal) 0
  simp [Real.fourierInv_eq,h0] at h
  apply Complex.ofReal_injective
  calc
    ((∫ R, signalInverse d R : ℝ) : ℂ) = ∫ R, (signalInverse d R : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = 0 := h
    _ = ((0 : ℝ) : ℂ) := rfl

lemma signalInverse_quadratic_bound {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : ∃ G : ℝ, 0 ≤ G ∧ ∀ R, (1+R^2)*|signalInverse d R| ≤ G := by
  let f := hc.toSchwartzMap hd
  let g := 𝓕 f
  refine ⟨SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 2 0 g,by positivity,?_⟩
  intro R
  have h0 := g.norm_le_seminorm ℂ R
  have h2 := g.norm_pow_mul_le_seminorm ℂ 2 R
  have hr : |signalInverse d R| ≤ ‖g R‖ := Complex.abs_re_le_norm (g R)
  rw [Real.norm_eq_abs,sq_abs] at h2
  nlinarith [sq_nonneg R,mul_le_mul_of_nonneg_left hr (sq_nonneg R)]

lemma conj_stdAddChar {P : ℕ} [NeZero P] (h : ZMod P) :
    conj (ZMod.stdAddChar h) = ZMod.stdAddChar (-h) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

/-- The exact Ramanujan coefficient in the joint law of Section 3. -/
def signalRamanujanC (P : ℕ) [NeZero P] (h : ZMod P) : ℂ :=
  ∑ u : (ZMod P)ˣ, ZMod.stdAddChar (-(u.val*h))

def signalRamanujan (P : ℕ) [NeZero P] (h : ZMod P) : ℝ :=
  (signalRamanujanC P h).re

lemma conj_signalRamanujanC {P : ℕ} [NeZero P] (h : ZMod P) :
    conj (signalRamanujanC P h) = signalRamanujanC P h := by
  classical
  simp only [signalRamanujanC,map_sum,conj_stdAddChar,neg_neg]
  exact Fintype.sum_equiv (Equiv.neg ((ZMod P)ˣ)) _ _ (by
    intro u
    simp [Equiv.neg_apply,Units.val_neg,neg_mul])

lemma signalRamanujan_complex {P : ℕ} [NeZero P] (h : ZMod P) :
    (signalRamanujan P h : ℂ) = signalRamanujanC P h :=
  Complex.conj_eq_iff_re.mp (conj_signalRamanujanC h)

lemma signalRamanujan_bound {P : ℕ} [NeZero P] (h : ZMod P) :
    |signalRamanujan P h| ≤ Fintype.card (ZMod P)ˣ := by
  apply (Complex.abs_re_le_norm (signalRamanujanC P h)).trans
  calc
    ‖signalRamanujanC P h‖ ≤ ∑ u : (ZMod P)ˣ, ‖ZMod.stdAddChar (-(u.val*h))‖ :=
      norm_sum_le _ _
    _ = Fintype.card (ZMod P)ˣ := by simp [ZMod.stdAddChar_apply,Circle.norm_coe]

lemma sum_stdAddChar_mul {P : ℕ} [NeZero P] (k : ZMod P) :
    ∑ h : ZMod P, ZMod.stdAddChar (k*h) = if k = 0 then (P : ℂ) else 0 := by
  classical
  split_ifs with hk
  · simp [hk]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar P hk)

lemma signalRamanujan_selector {P : ℕ} [NeZero P] (k : ZMod P) :
    ∑ h : ZMod P, signalRamanujanC P h * ZMod.stdAddChar (k*h) =
      if IsUnit k then (P : ℂ) else 0 := by
  classical
  simp only [signalRamanujanC,Finset.sum_mul]
  rw [Finset.sum_comm]
  have heq (u : (ZMod P)ˣ) : ∑ h : ZMod P,
      ZMod.stdAddChar (-(u.val*h))*ZMod.stdAddChar (k*h) =
        if u.val = k then (P : ℂ) else 0 := by
    simp_rw [← AddChar.map_add_eq_mul,show ∀ h : ZMod P, -(u.val*h)+k*h = (k-u.val)*h by intro; ring]
    rw [sum_stdAddChar_mul]
    simp [sub_eq_zero,eq_comm]
  simp_rw [heq]
  split_ifs with hk
  · rw [Finset.sum_eq_single hk.unit]
    · simp
    · intro u _ hne
      simp only [ite_eq_right_iff]
      intro hu
      exfalso
      exact hne (Units.ext (hu.trans hk.unit_spec.symm))
    · simp
  · apply Finset.sum_eq_zero
    intro u _
    rw [ite_eq_right]
    intro hu
    exact hk (hu ▸ u.isUnit)

/-- Joint law; its marginal over the residue coordinate has total mass one. -/
def signalJoint (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P] (h : ZMod P) (R : ℝ) : ℝ :=
  (signalBaseline α R+γ*signalRamanujan P h*signalInverse d R)/P

lemma signalJoint_smooth {α : ℝ} (_hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (h : ZMod P) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJoint α γ d P h) := by
  exact ((smooth_signalBaseline α).add
    (contDiff_const.mul (signalInverse_contDiff hd hc))).div_const _

lemma signalJoint_integrable {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (h : ZMod P) : Integrable (signalJoint α γ d P h) :=
  ((integrable_signalBaseline hα).add
    ((signalInverse_integrable hd hc).const_mul (γ*signalRamanujan P h))).div_const _

lemma integral_signalJoint {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (h0 : d 0 = 0)
    (P : ℕ) [NeZero P] (h : ZMod P) : ∫ R, signalJoint α γ d P h R = 1/P := by
  simp only [signalJoint]
  rw [integral_div,integral_add (integrable_signalBaseline hα)
    ((signalInverse_integrable hd hc).const_mul _),integral_const_mul,
    integral_signalBaseline hα,integral_signalInverse hd hc hr h0]
  ring

lemma fourier_add_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (v : ℝ) :
    𝓕 (fun x => f x+g x) v = 𝓕 f v+𝓕 g v := by
  simp only [Real.fourier_eq,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff v).2 hf)
    ((Real.fourierIntegral_convergent_iff v).2 hg)]

lemma fourierInv_add_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (v : ℝ) :
    𝓕⁻ (fun x => f x+g x) v = 𝓕⁻ f v+𝓕⁻ g v := by
  simp only [Real.fourierInv_eq_fourier_neg,fourier_add_integrable hf hg]

lemma fourierInv_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    𝓕⁻ (fun x => c*f x) v = c*𝓕⁻ f v := by
  simp only [Real.fourierInv_eq_fourier_neg,fourier_const_mul]

lemma fourierInv_signalJoint {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (P : ℕ) [NeZero P] (h : ZMod P) (v : ℝ) :
    𝓕⁻ (fun R => (signalJoint α γ d P h R : ℂ)) v =
      (P : ℂ)⁻¹ * (𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v+
        (γ : ℂ)*signalRamanujanC P h*d v) := by
  have heq : (fun R => (signalJoint α γ d P h R : ℂ)) =
      fun R => (P : ℂ)⁻¹*((signalBaseline α R : ℂ)+
        ((γ : ℂ)*signalRamanujanC P h)*(signalInverse d R : ℂ)) := by
    funext R
    simp only [signalJoint,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_inv,Complex.ofReal_natCast,signalRamanujan_complex]
    ring
  rw [heq,fourierInv_const_mul]
  erw [fourierInv_add_integrable
    (integrable_signalBaseline hα).ofReal (((signalInverse_integrable hd hc).ofReal).const_mul _),
    fourierInv_const_mul,signalInverse_inversion hd hc hr]
  rfl

/-- Exact positive-exponent joint Fourier transform, not a conditional moment assumption. -/
theorem signalJoint_fourier {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (P : ℕ) [NeZero P] (v : ℝ) (k : ZMod P) :
    ∑ h : ZMod P, (𝓕⁻ (fun R => (signalJoint α γ d P h R : ℂ)) v)*
      ZMod.stdAddChar (k*h) =
      (if k = 0 then 𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v else 0)+
      (if IsUnit k then (γ : ℂ)*d v else 0) := by
  classical
  simp_rw [fourierInv_signalJoint hα γ hd hc hr]
  calc
    _ = (P : ℂ)⁻¹ * ((𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v)*
          (∑ h : ZMod P, ZMod.stdAddChar (k*h))+
        (γ : ℂ)*d v*(∑ h : ZMod P, signalRamanujanC P h*ZMod.stdAddChar (k*h))) := by
      simp only [mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      all_goals apply Finset.sum_congr rfl; intro h _; ring
    _ = _ := by
      rw [sum_stdAddChar_mul,signalRamanujan_selector]
      have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
      split_ifs <;> field_simp [hP] <;> ring

/-- Small strengths give the actual positive law, with the source's quantitative
    two-sided domination. The choice is independent of the angular scale B. -/
theorem signalJoint_positive_strength {α : ℝ} (hα : 0 < α) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ γ₀ →
      (∀ h : ZMod P, ∀ R : ℝ, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
        signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) ∧
      ∀ v : ℝ, 2*γ*‖d v‖ ≤ 1/2 := by
  obtain ⟨c,C,hc0,_hC,htail⟩ := signalBaseline_quadratic_tails hα
  obtain ⟨G,hG,hgb⟩ := signalInverse_quadratic_bound hd hc
  let Cu : ℝ := Fintype.card (ZMod P)ˣ
  have hCu : 0 ≤ Cu := by dsimp [Cu]; positivity
  let f := hc.toSchwartzMap hd
  let D := SchwartzMap.seminorm ℂ 0 0 f
  have hD : 0 ≤ D := apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f
  have hdD (v : ℝ) : ‖d v‖ ≤ D := f.norm_le_seminorm ℂ v
  let γ₀ := min (c/(2*(Cu*G+1))) (1/(4*(D+1)))
  have hCG : 0 < Cu*G+1 := by positivity
  refine ⟨γ₀,by dsimp [γ₀]; positivity,fun γ hγ hγ₀ => ⟨?_,?_⟩⟩
  · intro h R
    have hsmall : γ*(Cu*G+1) ≤ c/2 := by
      have hh := hγ₀.trans (min_le_left (c/(2*(Cu*G+1))) (1/(4*(D+1))))
      have hh' := (le_div_iff₀ (by positivity : 0 < 2*(Cu*G+1))).mp hh
      nlinarith
    have hgb' := hgb R
    have hcb := signalRamanujan_bound h
    have hb : |γ*signalRamanujan P h*signalInverse d R| ≤ signalBaseline α R/2 := by
      have hprod : (1+R^2)*|γ*signalRamanujan P h*signalInverse d R| ≤ γ*Cu*G := by
        rw [abs_mul,abs_mul,abs_of_nonneg hγ]
        calc
          _ = γ*|signalRamanujan P h| *((1+R^2)*|signalInverse d R| ) := by ring
          _ ≤ γ*Cu*G := by gcongr
      have ht := (htail R).1
      have hpos : 0 < 1+R^2 := by positivity
      have ht' := (div_le_iff₀ hpos).mp ht
      nlinarith
    have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    dsimp [signalJoint]
    constructor
    · rw [div_le_div_iff₀ (by positivity : 0 < 2*(P : ℝ)) hP]
      nlinarith
    · rw [div_le_div_iff₀ hP (by positivity : 0 < 2*(P : ℝ))]
      nlinarith
  · intro v
    have hh := hγ₀.trans (min_le_right (c/(2*(Cu*G+1))) (1/(4*(D+1))))
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*(D+1))).mp hh
    have hbd := mul_le_mul_of_nonneg_left (hdD v) hγ
    nlinarith

/-- The manuscript's finite sieve modulus, unchanged (not a factorial proxy). -/
def signalPrimeProduct (L : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (L+1)).filter Nat.Prime, p

lemma signalPrimeProduct_pos (L : ℕ) : 0 < signalPrimeProduct L := by
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

instance (L : ℕ) : NeZero (signalPrimeProduct L) := ⟨(signalPrimeProduct_pos L).ne'⟩

lemma dvd_signalPrimeProduct {p L : ℕ} (hp : p.Prime) (hL : p ≤ L) :
    p ∣ signalPrimeProduct L := by
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩)

lemma signalPrimeProduct_ge_two {L : ℕ} (hL : 2 ≤ L) : 2 ≤ signalPrimeProduct L :=
  Nat.le_of_dvd (signalPrimeProduct_pos L) (dvd_signalPrimeProduct Nat.prime_two hL)

lemma signal_sieve_no_unit {L ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hL : ℓ ≤ L)
    (m : ZMod (signalPrimeProduct L)) : ¬ IsUnit ((ℓ : ZMod (signalPrimeProduct L))*m) := by
  intro h
  have hu := (ZMod.isUnit_iff_coprime ℓ (signalPrimeProduct L)).mp
    (isUnit_of_mul_isUnit_left h)
  have hp := Nat.minFac_prime (n := ℓ) (by omega)
  exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd ℓ)
    (dvd_signalPrimeProduct hp ((Nat.minFac_le (by omega)).trans hL))) hu

/-- The exact ideal integer moments, with only the first nonzero harmonic. -/
theorem signalJoint_sieved_moments {α b D x : ℝ} (hα : 0 < α) (hαb : α < b)
    (hb : 0 < b) (hx : b ≤ |x|) {L : ℕ} (hL : D/b < L)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hr : ∀ v, d (-v) = conj (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (γ : ℝ)
    (m : ZMod (signalPrimeProduct L)) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ h : ZMod (signalPrimeProduct L),
      (𝓕⁻ (fun R => (signalJoint α γ d (signalPrimeProduct L) h R : ℂ))) (ℓ*x)*
        ZMod.stdAddChar (((ℓ : ZMod (signalPrimeProduct L))*m)*h) =
      if ℓ = 1 ∧ IsUnit m then (γ : ℂ)*d x else 0 := by
  rw [signalJoint_fourier hα γ hd hc hr]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hav : α ≤ |(ℓ : ℝ)*x| := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)]
    nlinarith [abs_nonneg x]
  have hbase : 𝓕⁻ (fun R => (signalBaseline α R : ℂ)) ((ℓ : ℝ)*x) = 0 := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact signalBaseline_fourier_support hα (by simpa only [abs_neg] using hav)
  rw [hbase]
  simp only [ite_self,zero_add]
  by_cases he : ℓ = 1
  · subst ℓ
    simp
  · rw [ite_eq_right (show ¬ (ℓ = 1 ∧ IsUnit m) from fun h => he h.1)]
    by_cases hd0 : d ((ℓ : ℝ)*x) = 0
    · simp [hd0]
    · have hv := hs hd0
      have ha : |(ℓ : ℝ)*x| ≤ D := abs_le.mpr hv
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)] at ha
      have hbound : (ℓ : ℝ) < L := by
        have hcL := (div_lt_iff₀ hb).mp hL
        nlinarith
      have hℓL : ℓ ≤ L := (by exact_mod_cast hbound : ℓ < L).le
      rw [ite_eq_right (signal_sieve_no_unit (by omega) hℓL m)]

/-- All choices of the positive-law construction precede the angular scale.
    The interval support used below is the exact compact support condition on d. -/
theorem exists_signal_positive_law {b D : ℝ} (hb : 0 < b)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hr : ∀ v, d (-v) = conj (d v))
    (h0 : d 0 = 0) (hs : Function.support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
        (∀ h : ZMod (signalPrimeProduct L),
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJoint α γ d (signalPrimeProduct L) h) ∧
          Integrable (signalJoint α γ d (signalPrimeProduct L) h) ∧
          (∫ R, signalJoint α γ d (signalPrimeProduct L) h R) = 1/(signalPrimeProduct L) ∧
          ∀ R, signalBaseline α R/(2*(signalPrimeProduct L)) ≤
              signalJoint α γ d (signalPrimeProduct L) h R ∧
            signalJoint α γ d (signalPrimeProduct L) h R ≤
              3*signalBaseline α R/(2*(signalPrimeProduct L))) ∧
        (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
        ∀ x, b ≤ |x| → ∀ m : ZMod (signalPrimeProduct L), ∀ ℓ : ℕ, 1 ≤ ℓ →
          ∑ h : ZMod (signalPrimeProduct L),
            (𝓕⁻ (fun R => (signalJoint α γ d (signalPrimeProduct L) h R : ℂ))) (ℓ*x)*
              ZMod.stdAddChar (((ℓ : ZMod (signalPrimeProduct L))*m)*h) =
            if ℓ = 1 ∧ IsUnit m then (γ : ℂ)*d x else 0 := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max 2 (D/b))
  have hL2 : 2 ≤ L := by
    have hh : (2 : ℝ) < L := (le_max_left _ _).trans_lt hL
    exact_mod_cast hh.le
  have hLD : D/b < L := (le_max_right _ _).trans_lt hL
  have hα : 0 < b/4 := by positivity
  obtain ⟨γ₀,hγ₀,hγ⟩ := signalJoint_positive_strength hα hd hc (signalPrimeProduct L)
  refine ⟨b/4,L,γ₀,hα,by linarith,hL2,hLD,hγ₀,?_⟩
  intro γ hγpos hγle
  obtain ⟨hbound,hdBound⟩ := hγ γ hγpos.le hγle
  refine ⟨?_,hdBound,?_⟩
  · intro h
    exact ⟨signalJoint_smooth hα γ hd hc _ h,signalJoint_integrable hα γ hd hc _ h,
      integral_signalJoint hα γ hd hc hr h0 _ h,hbound h⟩
  · intro x hx m ℓ hℓ
    exact signalJoint_sieved_moments hα (by linarith) hb hx hLD hd hc hr hs γ m ℓ hℓ

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

def affineDensity (q : ℝ → ℝ) (a b y : ℝ) : ℝ := a*q (a*y+b)

lemma integrable_affineDensity {q : ℝ → ℝ} (hq : Integrable q) {a : ℝ}
    (ha : a ≠ 0) (b : ℝ) : Integrable (affineDensity q a b) := by
  exact ((integrable_comp_mul_left_iff (fun x => q (x+b)) ha).2
    (hq.comp_add_right b)).const_mul a

lemma integral_affineDensity {q : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ y, affineDensity q a b y) = ∫ y, q y := by
  unfold affineDensity
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun y => q (y+b)) a,
    integral_add_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr ha)]
  field_simp

lemma fourierInv_affineDensity {q : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (b v : ℝ) :
    𝓕⁻ (fun y => (affineDensity q a b y : ℂ)) v =
      Complex.exp ((-2*Real.pi*(v*b/a) : ℝ)*Complex.I)*
        𝓕⁻ (fun y => (q y : ℂ)) (v/a) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul]
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((2*Real.pi*v/a)*x : ℝ)*Complex.I)*(q x : ℂ)
  have hf : ∀ y : ℝ,
      Complex.exp (((-2*Real.pi*y*(-v)) : ℝ)*Complex.I)*
        (affineDensity q a b y : ℂ) =
      (a : ℂ)*(Complex.exp ((-2*Real.pi*(v*b/a) : ℝ)*Complex.I)*f (a*y+b)) := by
    intro y
    have hex : (-2*Real.pi*y*(-v)) =
        -2*Real.pi*(v*b/a)+(2*Real.pi*v/a)*(a*y+b) := by
      field_simp [ha.ne']
      ring
    dsimp only [affineDensity,f]
    rw [hex,Complex.ofReal_add,add_mul,Complex.exp_add]
    simp only [Complex.ofReal_mul]
    ring
  simp_rw [hf]
  rw [integral_const_mul,integral_const_mul,Measure.integral_comp_mul_left (fun y => f (y+b)) a,
    integral_add_right_eq_self]
  simp only [abs_of_pos (inv_pos.mpr ha),Complex.real_smul,Complex.ofReal_inv]
  have hg : (fun y : ℝ => Complex.exp (((-2*Real.pi*y*(-(v/a))) : ℝ)*Complex.I)*
      (q y : ℂ)) = f := by
    funext y
    dsimp [f]
    congr 2
    ring_nf
  rw [hg]
  field_simp [show (a : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr ha.ne']

lemma affine_square_bound (a b y : ℝ) :
    1+(a*y+b)^2 ≤ (1+2*a^2+2*b^2)*(1+y^2) := by
  nlinarith [sq_nonneg (a*y-b),sq_nonneg a,sq_nonneg y,
    mul_nonneg (sq_nonneg b) (sq_nonneg y)]

lemma affineDensity_quadratic_tails {q : ℝ → ℝ} {a c C : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C)
    (hq : ∀ y, c/(1+y^2) ≤ q y ∧ q y ≤ C/(1+y^2)) (b : ℝ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ y,
      c'/(1+y^2) ≤ affineDensity q a b y ∧
      affineDensity q a b y ≤ C'/(1+y^2) := by
  let K := 1+2*a^2+2*b^2
  let K' := 1+2*(a⁻¹)^2+2*(-b/a)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hK' : 0 < K' := by dsimp [K']; positivity
  refine ⟨a*c/K,a*C*K',by positivity,by positivity,fun y => ⟨?_,?_⟩⟩
  · have hbnd := affine_square_bound a b y
    have hp : 0 < 1+y^2 := by positivity
    have hp' : 0 < 1+(a*y+b)^2 := by positivity
    have he : a*c/K/(1+y^2) ≤ a*(c/(1+(a*y+b)^2)) := by
      rw [div_div,← mul_div_assoc]
      exact div_le_div_of_nonneg_left (by positivity) hp' (by simpa [K] using hbnd)
    exact he.trans (mul_le_mul_of_nonneg_left (hq _).1 ha.le)
  · have hbnd := affine_square_bound a⁻¹ (-b/a) (a*y+b)
    have he : a⁻¹*(a*y+b)+ -b/a = y := by field_simp [ha.ne']; ring
    rw [he] at hbnd
    have hp : 0 < 1+y^2 := by positivity
    have hp' : 0 < 1+(a*y+b)^2 := by positivity
    apply (mul_le_mul_of_nonneg_left (hq _).2 ha.le).trans
    rw [← mul_div_assoc,div_le_div_iff₀ hp' hp]
    have hh := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ a*C by positivity)
    dsimp [K'] at *
    nlinarith

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

lemma finite_sum_quadratic_tails {ι : Type*} [Fintype ι] [Nonempty ι]
    {q : ι → ℝ → ℝ}
    (hq : ∀ i, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y,
      c/(1+y^2) ≤ q i y ∧ q i y ≤ C/(1+y^2)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y,
      c/(1+y^2) ≤ ∑ i, q i y ∧ ∑ i, q i y ≤ C/(1+y^2) := by
  classical
  choose c C hc hC hbound using hq
  refine ⟨∑ i, c i,∑ i, C i,
    Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty,
    Finset.sum_pos (fun i _ => hC i) Finset.univ_nonempty,?_⟩
  intro y
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => (hbound i y).1
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => (hbound i y).2

/-- Density of J_*=(R/B+h/P)/c; the finite representatives are h.val. -/
def signalJitter (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B c y : ℝ) : ℝ :=
  c*B*∑ h : ZMod P, signalJoint α γ d P h (B*(c*y-h.val/P))

lemma signalJitter_affine (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B c y : ℝ) :
    signalJitter α γ d P B c y =
      ∑ h : ZMod P, affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y := by
  classical
  simp only [signalJitter,Finset.mul_sum,affineDensity]
  apply Finset.sum_congr rfl
  intro h _
  congr 2
  ring

lemma signalJitter_smooth {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (B c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJitter α γ d P B c) := by
  classical
  apply contDiff_const.mul
  apply ContDiff.sum
  intro h _
  exact (signalJoint_smooth hα γ hd hc P h).comp (by fun_prop)

lemma signalJitter_integrable {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] :
    Integrable (signalJitter α γ d P B c) := by
  simp only [show signalJitter α γ d P B c = fun y =>
    ∑ h : ZMod P, affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y from
      funext (signalJitter_affine α γ d P B c)]
  exact integrable_finsetSum _ (fun h _ => integrable_affineDensity
    (signalJoint_integrable hα γ hd hcomp P h) (mul_pos hc hB).ne' _)

lemma integral_signalJitter {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (h0 : d 0 = 0) (P : ℕ) [NeZero P] :
    (∫ y, signalJitter α γ d P B c y) = 1 := by
  simp_rw [signalJitter_affine]
  rw [integral_finsetSum _ (fun h _ => integrable_affineDensity
    (signalJoint_integrable hα γ hd hcomp P h) (mul_pos hc hB).ne' _)]
  simp_rw [integral_affineDensity (mul_pos hc hB),integral_signalJoint hα γ hd hcomp hr h0]
  simp [ZMod.card P,NeZero.ne P]

lemma signalJitter_quadratic_tails {α B c γ : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) {d : ℝ → ℂ} (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ y,
      a/(1+y^2) ≤ signalJitter α γ d P B c y ∧
      signalJitter α γ d P B c y ≤ A/(1+y^2) := by
  obtain ⟨a,A,ha,hA,hq⟩ := signalBaseline_quadratic_tails hα
  have hP : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
  have ht (h : ZMod P) : ∀ y, (a/(2*P))/(1+y^2) ≤ signalJoint α γ d P h y ∧
      signalJoint α γ d P h y ≤ (3*A/(2*P))/(1+y^2) := by
    intro y
    constructor
    · have hh := div_le_div_of_nonneg_right (hq y).1 (show 0 ≤ 2*(P:ℝ) by positivity)
      have hh' : a/(2*P)/(1+y^2) ≤ signalBaseline α y/(2*P) := by
        convert hh using 1; first | rfl | ring
      exact hh'.trans (hbound h y).1
    · have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hq y).2 (show 0 ≤ (3:ℝ) by norm_num))
        (show 0 ≤ 2*(P:ℝ) by positivity)
      exact (hbound h y).2.trans (by convert hh using 1; ring)
  obtain ⟨a',A',ha',hA',hbnd⟩ := finite_sum_quadratic_tails
    (fun h : ZMod P => affineDensity_quadratic_tails (mul_pos hc hB)
      (show 0 < a/(2*P) by positivity) (show 0 < 3*A/(2*P) by positivity) (ht h)
      (-B*h.val/P))
  exact ⟨a',A',ha',hA',fun y => by simpa only [signalJitter_affine] using hbnd y⟩

lemma signalJitter_pos {α B c γ : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) {d : ℝ → ℂ} (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) (y : ℝ) :
    0 < signalJitter α γ d P B c y := by
  obtain ⟨a,A,ha,_hA,hbnd⟩ := signalJitter_quadratic_tails hα hB hc P hbound
  exact lt_of_lt_of_le (by positivity : 0 < a/(1+y^2)) (hbnd y).1

lemma fourierInv_finsetSum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ S, Integrable (f i)) (v : ℝ) :
    𝓕⁻ (fun y => ∑ i ∈ S, f i y) v = ∑ i ∈ S, 𝓕⁻ (f i) v := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_eq,Finset.smul_sum]
  exact integral_finsetSum S (fun i hi => (Real.fourierIntegral_convergent_iff (-v)).2 (hf i hi))

lemma signalJitter_fourierInv {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] (v : ℝ) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) v =
      ∑ h : ZMod P, Complex.exp ((2*Real.pi*(v*h.val/(c*P)) : ℝ)*Complex.I)*
        𝓕⁻ (fun y => (signalJoint α γ d P h y : ℂ)) (v/(c*B)) := by
  classical
  have he : (fun y => (signalJitter α γ d P B c y : ℂ)) = fun y =>
      ∑ h : ZMod P, (affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y : ℂ) := by
    funext y
    rw [signalJitter_affine]
    push_cast
    rfl
  rw [he]
  erw [fourierInv_finsetSum _ (fun h _ =>
    (integrable_affineDensity (signalJoint_integrable hα γ hd hcomp P h)
      (mul_pos hc hB).ne' _).ofReal)]
  apply Finset.sum_congr rfl
  intro h _
  erw [fourierInv_affineDensity (mul_pos hc hB)]
  congr 3
  field_simp [hB.ne',hc.ne',show (P : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne P)]

lemma signal_character (P : ℕ) [NeZero P] (n : ℤ) (h : ZMod P) :
    ZMod.stdAddChar ((n : ZMod P)*h) =
      Complex.exp ((2*Real.pi*((n:ℝ)*h.val/P) : ℝ)*Complex.I) := by
  have he := ZMod.stdAddChar_coe (N := P) (n*(h.val:ℤ))
  simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val] at he
  rw [he]
  push_cast
  congr 1
  ring

lemma signalJitter_integer_moments {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] (n : ℤ) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) ((n:ℝ)*c) =
      ∑ h : ZMod P, (𝓕⁻ (fun y => (signalJoint α γ d P h y : ℂ))) ((n:ℝ)/B)*
        ZMod.stdAddChar ((n : ZMod P)*h) := by
  rw [signalJitter_fourierInv hα hB hc γ hd hcomp]
  have he : (n:ℝ)*c/(c*B) = (n:ℝ)/B := by field_simp
  rw [he]
  apply Finset.sum_congr rfl
  intro h _
  rw [signal_character,mul_comm]
  congr 3
  field_simp

lemma signalJitter_sieved_moments {α B c b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hB : 0 < B) (hc : 0 < c) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    𝓕⁻ (fun y => (signalJitter α γ d (signalPrimeProduct L) B c y : ℂ))
      ((ℓ:ℝ)*(m:ℝ)*c) =
      if ℓ = 1 ∧ IsUnit (m : ZMod (signalPrimeProduct L)) then (γ : ℂ)*d ((m:ℝ)/B) else 0 := by
  have he := signalJitter_integer_moments hα hB hc γ hd hcomp (signalPrimeProduct L)
    ((ℓ:ℤ)*m)
  push_cast at he
  rw [he]
  have hh := signalJoint_sieved_moments hα hαb hb hm hL hd hcomp hr hs γ
    (m : ZMod (signalPrimeProduct L)) ℓ hℓ
  convert hh using 1
  congr 2
  ring_nf

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace ThreeTorus

/-- Density under multiplication by a nonzero real scale, including negative scales. -/
def scaledDensity (q : ℝ → ℝ) (s y : ℝ) : ℝ := |s|⁻¹*q (y/s)

lemma integrable_scaledDensity {q : ℝ → ℝ} (hq : Integrable q) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledDensity q s) := by
  have hi := ((integrable_comp_mul_left_iff q (inv_ne_zero hs)).2 hq).const_mul |s|⁻¹
  change Integrable (fun y => |s|⁻¹*q (y/s))
  simpa only [div_eq_mul_inv,mul_comm] using hi

lemma integral_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    (∫ y, scaledDensity q s y) = ∫ y, q y := by
  simp only [scaledDensity,div_eq_mul_inv]
  rw [integral_const_mul,Measure.integral_comp_mul_right]
  simp only [inv_inv,smul_eq_mul]
  field_simp

lemma fourierInv_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕⁻ (fun y => (scaledDensity q s y : ℂ)) v =
      𝓕⁻ (fun y => (q y : ℂ)) (v*s) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul]
  let f : ℝ → ℂ := fun x => Complex.exp (((-2*Real.pi*x*(-(v*s))) : ℝ)*Complex.I)*(q x : ℂ)
  have he : ∀ y : ℝ,
      Complex.exp (((-2*Real.pi*y*(-v)) : ℝ)*Complex.I)*(scaledDensity q s y : ℂ) =
        ((|s| : ℝ) : ℂ)⁻¹*f (s⁻¹*y) := by
    intro y
    have harg : -2*Real.pi*(s⁻¹*y)*(-(v*s)) = -2*Real.pi*y*(-v) := by
      field_simp [hs]
    dsimp only [f,scaledDensity]
    rw [harg]
    simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
    rw [mul_comm s⁻¹ y]
    ring
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  simp only [inv_inv,Complex.real_smul]
  have hsC : ((|s| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hs)
  field_simp
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp only [f]
  congr 3
  ring_nf

lemma fourier_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕 (fun y => (scaledDensity q s y : ℂ)) v = 𝓕 (fun y => (q y : ℂ)) (v*s) := by
  have hh := fourierInv_scaledDensity (q := q) hs (-v)
  simpa only [Real.fourierInv_eq_fourier_neg,neg_neg,neg_mul,neg_neg] using hh

lemma scaledDensity_quadratic_bound {q : ℝ → ℝ} {C s : ℝ} (hC : 0 ≤ C) (hs : s ≠ 0)
    (hq : ∀ y, |q y| ≤ C/(1+y^2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y, |scaledDensity q s y| ≤ D/(1+y^2) := by
  let K := 1+2*s^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨|s|⁻¹*C*K,by positivity,fun y => ?_⟩
  have hsq : y^2 = s^2*(y/s)^2 := by field_simp
  have hbnd : 1+y^2 ≤ K*(1+(y/s)^2) := by
    dsimp [K]
    nlinarith [sq_nonneg s,sq_nonneg (y/s)]
  calc
    |scaledDensity q s y| = |s|⁻¹*|q (y/s)| := by
      simp only [scaledDensity,abs_mul,abs_inv,abs_abs]
    _ ≤ |s|⁻¹*(C/(1+(y/s)^2)) := mul_le_mul_of_nonneg_left (hq _) (by positivity)
    _ ≤ (|s|⁻¹*C*K)/(1+y^2) := by
      rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbnd (show 0 ≤ |s|⁻¹*C by positivity)]

lemma quadratic_norm_isBigO {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ C/(1+y^2)) :
    f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2:ℝ))) := by
  apply IsBigO.of_bound C
  filter_upwards [(isCompact_Icc (a := (-1:ℝ)) (b := 1)).compl_mem_cocompact] with y hy
  have h0 : y ≠ 0 := by intro h; subst y; simp at hy
  have hsq : 0 < y^2 := sq_pos_of_ne_zero h0
  have hr : |y| ^ (-(2:ℝ)) = (y^2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg y),Real.rpow_two,sq_abs]
  rw [hr,Real.norm_eq_abs,abs_of_nonneg (by positivity),← div_eq_mul_inv]
  exact (hf y).trans (div_le_div_of_nonneg_left hC hsq (by nlinarith))

lemma summable_lattice_of_bounded_support {f : ℝ → ℂ} {D : ℝ}
    (hf : ∀ v, D < |v| → f v = 0) : Summable (fun n : ℤ => f (n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt D
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(N:ℤ)) N)
  intro n hn
  apply hf
  by_contra! hh
  have hab := abs_le.mp (hh.trans hN.le)
  exact hn (Finset.mem_Icc.mpr ⟨by exact_mod_cast hab.1,by exact_mod_cast hab.2⟩)

/-- Exact Poisson expansion for every continuously bandlimited quadratic-tail law. -/
theorem periodization_fourier {q : ℝ → ℝ} (hq : Continuous q) {C : ℝ} (hC : 0 ≤ C)
    (hbnd : ∀ y, |q y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0) (x : ℝ) :
    ∑' n : ℤ, (q (x+n) : ℂ) =
      ∑' n : ℤ, 𝓕 (fun y => (q y : ℂ)) (n:ℝ)*fourier n (x : UnitAddCircle) := by
  apply Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hq) (b := 2) (by norm_num)
  · exact quadratic_norm_isBigO hC (fun y => by simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbnd y)
  · exact summable_lattice_of_bounded_support hF

lemma fourierInv_real_neg (q : ℝ → ℝ) (v : ℝ) :
    𝓕⁻ (fun y => (q y : ℂ)) (-v) = starRingEnd ℂ (𝓕⁻ (fun y => (q y : ℂ)) v) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I]
  congr 2
  push_cast
  ring

lemma periodization_three_modes {q : ℝ → ℝ} (hq : Continuous q) {C : ℝ} (hC : 0 ≤ C)
    (hbnd : ∀ y, |q y| ≤ C/(1+y^2)) (a : ℂ)
    (hmom : ∀ n : ℤ, 𝓕⁻ (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then a else if n = -1 then starRingEnd ℂ a else 0)
    (x : ℝ) :
    ∑' n : ℤ, (q (x+n) : ℂ) = 1 + 2*((a * fourier (-1) (x : UnitAddCircle)).re : ℂ) := by
  have hF (n : ℤ) : 𝓕 (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then starRingEnd ℂ a else if n = -1 then a else 0 := by
    have hh := hmom (-n)
    simp only [Int.cast_neg,Real.fourierInv_eq_fourier_neg,neg_neg] at hh
    rw [hh]
    by_cases h0 : n = 0
    · simp [h0]
    by_cases h1 : n = 1
    · simp [h1]
    by_cases hn1 : n = -1
    · simp [hn1]
    have hh1 : -n ≠ 1 := by omega
    have hh2 : -n ≠ -1 := by omega
    simp [h0,h1,hn1,hh1,hh2]
  have hs : Summable (fun n : ℤ => 𝓕 (fun y => (q y : ℂ)) (n:ℝ)) := by
    apply summable_of_ne_finset_zero (s := {-1,0,1})
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [hF,hn.1,hn.2.1,hn.2.2]
  have hh := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hq) (b := 2) (by norm_num)
    (quadratic_norm_isBigO hC (fun y => by
      simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbnd y)) hs x
  simp only [Function.comp_def] at hh
  erw [hh]
  rw [tsum_eq_sum (s := {-1,0,1}) (fun n hn => by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [hF,hn.1,hn.2.1,hn.2.2])]
  simp only [Finset.sum_insert,Finset.sum_singleton,show (-1 : ℤ) ∉ ({0,1} : Finset ℤ) by decide,
    show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide,not_false_eq_true,hF]
  norm_num only [fourier_zero,Int.reduceNeg,Int.reduceEq,ite_true,ite_false,one_mul,mul_one]
  rw [fourier_neg]
  have he : a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle)) +
      starRingEnd ℂ a * fourier 1 (x : UnitAddCircle) =
      2*((a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle))).re : ℂ) := by
    simpa only [map_mul,starRingEnd_self_apply,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.add_conj (a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle)))
  linear_combination he

/-- A compact Fourier bandwidth supplies a shared finite series near any nonzero scale. -/
lemma periodization_scaled_finite {q : ℝ → ℝ} (hq : Continuous q)
    {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D ε : ℝ} (hε : 0 < ε) (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {N : ℕ} (hN : D < N*ε) {s : ℝ} (hs : ε ≤ |s|) (x : ℝ) :
    ∑' n : ℤ, (scaledDensity q s (x+n) : ℂ) =
      ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
        𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s)*fourier n (x : UnitAddCircle) := by
  have hs0 : s ≠ 0 := by intro hh; simp [hh] at hs; linarith
  obtain ⟨C',hC',hbound⟩ := scaledDensity_quadratic_bound hC hs0 hbnd
  have hcont : Continuous (scaledDensity q s) :=
    continuous_const.mul (hq.comp (continuous_id.div_const _))
  have hband (n : ℤ) (hn : n ∉ Finset.Icc (-(N:ℤ)) N) :
      𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s) = 0 := by
    apply hF
    have hn' : (N : ℝ) < |(n:ℝ)| := by
      by_contra! hab
      have hle := abs_le.mp hab
      apply hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hle.1,by exact_mod_cast hle.2⟩
    rw [abs_mul]
    exact hN.trans_le (mul_le_mul (le_of_lt hn') hs hε.le (abs_nonneg _))
  have hsumm : Summable (fun n : ℤ => 𝓕 (fun y => (scaledDensity q s y : ℂ)) (n:ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N:ℤ)) N)
    intro n hn
    rw [fourier_scaledDensity hs0]
    exact hband n hn
  have he := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hcont) (b := 2) (by norm_num)
    (quadratic_norm_isBigO hC' (fun y => by
      simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbound y)) hsumm x
  simp only [Function.comp_def] at he
  erw [he]
  simp_rw [fourier_scaledDensity hs0]
  exact tsum_eq_sum (fun n hn => by rw [hband n hn,zero_mul])

lemma periodization_scaled_tendstoUniformly {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    TendstoUniformly (fun s x => ∑' n : ℤ, (scaledDensity q s (x+n) : ℂ))
      (fun x => ∑' n : ℤ, (scaledDensity q s₀ (x+n) : ℂ)) (𝓝 s₀) := by
  let ε := |s₀|/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (D/ε)
  have hN' : D < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  let S := Finset.Icc (-(N:ℤ)) N
  let F : ℝ → ℂ := 𝓕 (fun y => (q y : ℂ))
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hqi.ofReal
  let G : ℝ → UnitAddCircle → ℂ := fun s x => ∑ n ∈ S, F ((n:ℝ)*s)*fourier n x
  have hGc : Continuous ↿G := by
    change Continuous (fun p : ℝ × UnitAddCircle => ∑ n ∈ S, F ((n:ℝ)*p.1)*fourier n p.2)
    apply continuous_finsetSum _
    intro n _
    exact (hFc.comp (continuous_const.mul continuous_fst)).mul
      ((fourier n).continuous.comp continuous_snd)
  have hu := Continuous.tendstoUniformly G hGc s₀
  have hnear : ∀ᶠ s : ℝ in 𝓝 s₀, ε ≤ |s| := by
    have hh : ε < |s₀| := by dsimp [ε]; linarith [abs_pos.mpr hs₀]
    exact ((continuous_abs.tendsto s₀).eventually (eventually_gt_nhds hh)).mono
      (fun _ h => h.le)
  have hs₀' : ε ≤ |s₀| := by dsimp [ε]; linarith [abs_nonneg s₀]
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ,hnear] with s hs hs'
  intro x
  rw [periodization_scaled_finite hq hC hbnd hε hF hN' hs' x,
    periodization_scaled_finite hq hC hbnd hε hF hN' hs₀' x]
  exact hs (x : UnitAddCircle)

lemma fourierInv_real_zero (q : ℝ → ℝ) :
    𝓕⁻ (fun y => (q y : ℂ)) 0 = ((∫ y, q y : ℝ) : ℂ) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    neg_zero,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul]
  exact integral_ofReal

lemma fourierInv_real_int_moments {q : ℝ → ℝ} (hmass : (∫ y, q y) = 1) (a : ℂ)
    (hpos : ∀ ℓ : ℕ, 1 ≤ ℓ → 𝓕⁻ (fun y => (q y : ℂ)) (ℓ:ℝ) = if ℓ = 1 then a else 0)
    (n : ℤ) :
    𝓕⁻ (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then a else if n = -1 then starRingEnd ℂ a else 0 := by
  by_cases h0 : n = 0
  · rw [h0,Int.cast_zero,ite_eq_left rfl,fourierInv_real_zero,hmass,Complex.ofReal_one]
  rcases lt_or_gt_of_ne h0 with hn | hn
  · have hneg : 0 ≤ -n := by omega
    let k := (-n).toNat
    have hk : (k : ℤ) = -n := Int.toNat_of_nonneg hneg
    have hkpos : 1 ≤ k := by omega
    have hnk : n = -(k : ℤ) := by omega
    rw [hnk,Int.cast_neg,Int.cast_natCast,fourierInv_real_neg,hpos k hkpos]
    by_cases hk1 : k = 1
    · simp [hk1]
    · have hk0 : k ≠ 0 := by omega
      have hn1 : -(k:ℤ) ≠ 1 := by omega
      have hnm1 : -(k:ℤ) ≠ -1 := by omega
      simp [hk1,hk0,hn1,hnm1]
  · lift n to ℕ using hn.le with k hk
    have hkpos : 1 ≤ k := by omega
    rw [Int.cast_natCast,hpos k hkpos]
    by_cases hk1 : k = 1
    · simp [hk1]
    · have hk0 : k ≠ 0 := by omega
      have hkn1 : (k:ℤ) ≠ -1 := by omega
      simp [hk1,hk0,hkn1]

end ThreeTorus

namespace ThreeTorus

lemma signalJitter_fourierInv_support {α B c D : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) (hαD : α ≤ D) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (P : ℕ) [NeZero P] {v : ℝ}
    (hv : c*B*D < |v|) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) v = 0 := by
  rw [signalJitter_fourierInv hα hB hc γ hd hcomp]
  have hdiv : D < |v/(c*B)| := by
    rw [abs_div,abs_of_pos (mul_pos hc hB),lt_div_iff₀ (mul_pos hc hB)]
    nlinarith
  apply Finset.sum_eq_zero
  intro h _
  rw [fourierInv_signalJoint hα γ hd hcomp hr]
  have hbase : 𝓕⁻ (fun y => (signalBaseline α y : ℂ)) (v/(c*B)) = 0 := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact signalBaseline_fourier_support hα (by simpa only [abs_neg] using hαD.trans hdiv.le)
  have hd0 : d (v/(c*B)) = 0 := by
    apply Function.notMem_support.mp
    intro hn
    have hh := hs hn
    exact (not_le_of_gt hdiv) (abs_le.mpr ⟨hh.1,hh.2⟩)
  rw [hbase,hd0,mul_zero,add_zero,mul_zero,mul_zero]

lemma signalJitter_scale_cancel {α γ : ℝ} (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B : ℝ) {c : ℝ} (hc : 0 < c) (m y : ℝ) :
    scaledDensity (signalJitter α γ d P B c) (m*c) y =
      scaledDensity (signalJitter α γ d P B 1) m y := by
  simp only [scaledDensity,signalJitter,abs_mul,abs_of_pos hc,mul_inv_rev,one_mul]
  by_cases hm : m = 0
  · simp [hm]
  have he : c*(y/(m*c)) = y/m := by field_simp
  rw [he]
  field_simp

lemma signalJitter_periodic_ideal {α B c b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hB : 0 < B) (hc : 0 < c) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L)) (y : ℝ) :
    ∑' k : ℤ, (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
      ((m:ℝ)*c) (y+k) : ℂ) =
      1 + 2*((((if IsUnit (m : ZMod (signalPrimeProduct L)) then (γ:ℂ)*d ((m:ℝ)/B) else 0) *
        fourier (-1) (y : UnitAddCircle)).re) : ℂ) := by
  have hm0 : (m:ℝ) ≠ 0 := by intro hh; rw [hh,zero_div,abs_zero] at hm; linarith
  have hmc : (m:ℝ)*c ≠ 0 := mul_ne_zero hm0 hc.ne'
  obtain ⟨a,A,_ha,hA,hbnd⟩ := signalJitter_quadratic_tails hα hB hc
    (signalPrimeProduct L) hbound
  have hqb : ∀ y, |signalJitter α γ d (signalPrimeProduct L) B c y| ≤ A/(1+y^2) := by
    intro y
    rw [abs_of_pos (signalJitter_pos hα hB hc _ hbound y)]
    exact (hbnd y).2
  obtain ⟨C,hC,hCb⟩ := scaledDensity_quadratic_bound hA.le hmc hqb
  have hcq : Continuous (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
      ((m:ℝ)*c)) := continuous_const.mul
    ((signalJitter_smooth hα γ hd hcomp _ B c).continuous.comp (continuous_id.div_const _))
  apply periodization_three_modes hcq hC hCb
  apply fourierInv_real_int_moments
  · rw [integral_scaledDensity hmc,integral_signalJitter hα hB hc γ hd hcomp hr h0]
  · intro ℓ hℓ
    erw [fourierInv_scaledDensity hmc]
    have he : (ℓ:ℝ)*((m:ℝ)*c) = (ℓ:ℝ)*(m:ℝ)*c := by ring
    rw [he,signalJitter_sieved_moments hα hαb hB hc hb hL γ hd hcomp hr hs m hm ℓ hℓ]
    split_ifs <;> simp_all

end ThreeTorus

namespace ThreeTorus

/-- The finite-c approximation is uniform on every fixed old speed range.
The exact ideal law is independent of c after scaling, as required in section 3. -/
lemma periodization_scaled_uniform_perturbation {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {s₀ : ℝ} (hs₀ : s₀ ≠ 0) (V : ℝ) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop, ∀ v : ℝ, |v| ≤ V → ∀ y : ℝ,
      dist (∑' n : ℤ, (scaledDensity q (s₀*(1+v/c)) (y+n) : ℂ))
        (∑' n : ℤ, (scaledDensity q s₀ (y+n) : ℂ)) < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendstoUniformly_iff.mp
      (periodization_scaled_tendstoUniformly hq hqi hC hbnd hF hs₀) ε hε)
  filter_upwards [eventually_gt_atTop (|s₀| * |V|/δ+1)] with c hc
  intro v hv y
  have hc0 : 0 < c := lt_trans (by positivity) hc
  have hv' : |v| ≤ |V| := hv.trans (le_abs_self V)
  have hnear : dist (s₀*(1+v/c)) s₀ < δ := by
    rw [Real.dist_eq,show s₀*(1+v/c)-s₀ = s₀*v/c by ring,
      abs_div,abs_mul,abs_of_pos hc0]
    apply (div_lt_iff₀ hc0).mpr
    have hh : |s₀| * |V| < δ*c := by
      have h := (div_lt_iff₀ hδ).mp (lt_trans (lt_add_one _) hc)
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hv' (abs_nonneg _)) hh
  simpa only [dist_comm] using hd hnear y

end ThreeTorus

namespace ThreeTorus

/-- The actual finite-c signal law, uniform in the bounded old speed and in
all phases. The modulus and strength are the exact fixed ones of the manuscript. -/
lemma signalJitter_periodic_approximation {α B b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hαD : α ≤ D) (hB : 0 < B) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L)) (V : ℝ) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop, ∀ v : ℝ, |v| ≤ V → ∀ y : ℝ,
      dist (∑' k : ℤ, (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
        ((m:ℝ)*(c+v)) (y+k) : ℂ))
      (1 + 2*((((if IsUnit (m : ZMod (signalPrimeProduct L)) then (γ:ℂ)*d ((m:ℝ)/B) else 0) *
        fourier (-1) (y : UnitAddCircle)).re) : ℂ)) < ε := by
  have hm0 : (m:ℝ) ≠ 0 := by intro hh; rw [hh,zero_div,abs_zero] at hm; linarith
  obtain ⟨a,A,_ha,hA,hbnd⟩ := signalJitter_quadratic_tails hα hB zero_lt_one
    (signalPrimeProduct L) hbound
  have hqb : ∀ y, |signalJitter α γ d (signalPrimeProduct L) B 1 y| ≤ A/(1+y^2) := by
    intro y
    rw [abs_of_pos (signalJitter_pos hα hB zero_lt_one _ hbound y)]
    exact (hbnd y).2
  have hF : ∀ v, B*D < |v| →
      𝓕 (fun y => (signalJitter α γ d (signalPrimeProduct L) B 1 y : ℂ)) v = 0 := by
    intro v hv
    have hh := signalJitter_fourierInv_support hα hB zero_lt_one hαD γ hd hcomp hr hs
      (signalPrimeProduct L) (v := -v) (by simpa only [one_mul,abs_neg] using hv)
    simpa only [Real.fourierInv_eq_fourier_neg,neg_neg] using hh
  intro ε hε
  have he := periodization_scaled_uniform_perturbation
    (signalJitter_smooth hα γ hd hcomp _ B 1).continuous
    (signalJitter_integrable hα hB zero_lt_one γ hd hcomp _)
    hA.le hqb hF hm0 V ε hε
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with c hc hc0
  intro v hv y
  have hscale : (m:ℝ)*(c+v) = ((m:ℝ)*(1+v/c))*c := by field_simp
  simp_rw [hscale,signalJitter_scale_cancel d (signalPrimeProduct L) B hc0]
  have hideal := signalJitter_periodic_ideal hα hαb hB zero_lt_one hb hL γ hd hcomp hr h0 hs
    m hm hbound y
  simp only [mul_one] at hideal
  rw [← hideal]
  exact hc v hv y

end ThreeTorus

end

end

end

end

end

end OAI
