import OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseMomentFirstProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = logPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-(9/2:ℝ)*L - ∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, logPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, logPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 9 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 9) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity logPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 9) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 9 → ℝ) (b : ℝ)
    (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.firstBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.firstBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 9 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 9 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (firstKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 9 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := paperRadialFourier_log_separation_envelope Φ box
    firstKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 9) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 9) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 9), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 9)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, firstLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, firstRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 9), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) firstLeftSlope firstRightSlope firstKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      firstLeftSlope firstRightSlope firstKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;>
      (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 9 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.firstBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-(9/2:ℝ)*L)*Real.exp (InverseClippingProfiles.firstRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.firstBalancedSlope,
    InverseClippingProfiles.firstRootExponent, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CubicReflectionKernel.logSchwartz_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 9 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile firstPoissonProfile
  rw [InverseClippingProfiles.firstRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, firstLeftSlope i*y i) *
    g₁ ((∑ i, firstLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, firstRightSlope i*y i) *
    g₂ ((∑ i, firstRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) * he

theorem first_profile_common_measure
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ,
        (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 9), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

end SevenEighths.InverseMomentFirstProfileUniform

end

end OAI
