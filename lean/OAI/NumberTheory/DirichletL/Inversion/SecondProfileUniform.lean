import OAI.NumberTheory.DirichletL.Inversion.InitialProfile
import OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

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

def normalization (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-6*L - ∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
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

theorem density_norm (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, logPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 6 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 6) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity logPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 6) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 6 → ℝ) (b : ℝ)
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.secondBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.secondBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 6 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 6 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (secondKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 6 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := paperRadialFourier_log_separation_envelope Φ box
    secondKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 6) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 6) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
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

theorem density_weighted_integral (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 6), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 6)) :
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

def profile (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 6), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| * B i)+Real.log b)
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
      Φ (fun i => translated (g i) (ρ i)) secondLeftSlope secondRightSlope secondKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
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

theorem balanced_exponential_identity (ρ y : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.secondBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-6*L)*Real.exp (InverseClippingProfiles.secondRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.secondBalancedSlope,
    InverseClippingProfiles.secondRootExponent, secondLeftSlope, secondRightSlope,
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
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 6 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-6*L) : ℂ) * secondPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, secondLeftSlope i*y i) *
    g₁ ((∑ i, secondLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, secondRightSlope i*y i) *
    g₂ ((∑ i, secondRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) * he

theorem second_profile_common_measure
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
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

def densityTower {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i z.1) (inheritedRight j z.1) L z.2

theorem densityTower_joint_measurable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    StronglyMeasurable (densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) := by
  unfold densityTower
  apply StronglyMeasurable.mul
  · exact ((InverseAmbientProfileTower.fullProfileDensity_continuous outer b₁ b₂ b₃).comp
      continuous_fst).stronglyMeasurable
  · have hm : Measurable (fun z : Ambient ι × Ambient (Fin 6) =>
        ((ρ,(c₁,c₂),(inheritedLeft i z.1,inheritedRight j z.1),L),z.2)) := by
      unfold inheritedLeft inheritedRight
      fun_prop
    exact (density_joint_measurable g g₁ g₂ c₃).comp_measurable hm

theorem densityTower_norm {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) :
    ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖ =
      normalization ρ c₁ c₂ L *
        ‖InverseAmbientProfileTower.towerDensity i j outer b₁ b₂ b₃ g g₁ g₂ c₃ z‖ := by
  simp only [densityTower, InverseAmbientProfileTower.towerDensity, norm_mul, density_norm]
  ring

theorem densityTower_weighted_integrable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (J : ℕ) :
    Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) := by
  obtain ⟨C,hC,h⟩ := InverseAmbientProfileTower.towerDensity_weighted (ι := ι) J g g₁ g₂ c₃
  convert (h i j outer b₁ b₂ b₃).1.const_mul (normalization ρ c₁ c₂ L) using 1
  funext z
  rw [densityTower_norm]
  ring

private theorem tower_bound_from_inner {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L C R : ℝ) (hC : 0 ≤ C) (_hR : 0 < R) (A J : ℕ)
    (hb : ∀ θ₁ θ₂ : ℝ, (1+R)^A * (∫ q : Ambient (Fin 6), ambientWeight J q *
        ‖density g g₁ g₂ c₃ ρ c₁ c₂ θ₁ θ₂ L q‖) ≤
      C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
        (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J))) :
    (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) ≤
      C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  let f := fun z : Ambient ι × Ambient (Fin 6) =>
    ambientWeight J z.1 * ambientWeight J z.2 *
      ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖
  have hi : Integrable f := densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J
  have hi' : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) := hi.const_mul _
  have hout := (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable
    outer b₁ b₂ b₃ (requiredOuterOrder J)).const_mul C
  change (1+R)^A*(∫ z, f z) ≤ _
  rw [← integral_const_mul]
  rw [show (∫ z : Ambient ι × Ambient (Fin 6), (1+R)^A*f z) =
      ∫ p : Ambient ι, ∫ q : Ambient (Fin 6), (1+R)^A*f (p,q) by
    simpa only [Measure.volume_eq_prod] using integral_prod _ hi']
  rw [← integral_const_mul]
  have hip : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi'
  apply integral_mono hip.integral_prod_left hout
  intro p
  dsimp only
  have he : (∫ q : Ambient (Fin 6), (1+R)^A*f (p,q)) =
      ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖ *
        ((1+R)^A * ∫ q : Ambient (Fin 6), ambientWeight J q *
          ‖density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i p) (inheritedRight j p) L q‖) := by
    simp only [f, densityTower, norm_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    ring
  rw [he]
  have hw := inherited_pair_weight_bound i j J (InverseClippingProfiles.momentOrder J) p
  have hp : 0 ≤ ambientWeight J p := zero_le_one.trans (ambientWeight_one_le J p)
  calc
    _ ≤ (ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (C*((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) :=
      mul_le_mul_of_nonneg_left (hb _ _) (mul_nonneg hp (norm_nonneg _))
    _ = (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (ambientWeight J p * ((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) := by ring
    _ ≤ (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) * ambientWeight (requiredOuterOrder J) p :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

theorem second_profile_tower_uniform {ι : Type*} [Fintype ι]
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := second_profile_common_measure U g₁ g₂ Φ M B m₁ m₂ b hM hB hU h₁ h₂ A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,hc₃⟩ := hs R hR
  refine ⟨c₃,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).1, ?_⟩
  intro i j outer b₁ b₂ b₃
  refine ⟨densityTower_weighted_integrable i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L J, ?_⟩
  exact tower_bound_from_inner i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L C R hC hR A J
    (fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).2.2)

theorem densityTower_fubini {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ)
    (F : Ambient ι × Ambient (Fin 6) → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z * F z) =
      ∫ p, ∫ q, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L (p,q) * F (p,q) :=
  density_test_fubini _ F
    (densityTower_joint_measurable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) hF J
    (densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J) hbound

theorem actual_child_height_weight_bound (J K : ℕ) (p : Ambient (Fin 6)) :
    ambientWeight J p *
      ((1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4‖)^K *
       (1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5‖)^K) ≤
      ambientWeight (J+2*K) p := by
  simpa only [second_inherited_left_eq, second_inherited_right_eq, norm_neg] using
    inherited_pair_weight_bound (4 : Fin 6) 5 J K p

theorem normalization_eta_log (Z η : ℝ) (hZ : 0 < Z) :
    Real.exp (-6*(η*Real.log Z)) = Z^(-6*η) := by
  rw [Real.rpow_def_of_pos hZ]
  congr 1
  ring

theorem fresh_physical_profile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hω₁ : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1)
    (hω₂ : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1)
    (hcut : ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
      ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L) : ℂ) * secondNormProfile
      (fun x => W₁ (x/(G₀*V₀*X₀))) (fun x => W₂ (x/(G₀*V₀*X₀)))
      Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ) : ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
        ((Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V
          (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀)) := by
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₁.symm.trans (hω₁ hn))
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₂.symm.trans (hω₂ hn))
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀))*secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm, secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV hK hX q hq]
  change _*( _*(_*secondNormProfile W₁ W₂ Φ (fun _ _ => 1) _
    (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀))) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV hK hX) (hcut hw₁ hw₂)]
  ring_nf
  rfl

theorem retained_clipping_parameter (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hret : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧ |Real.log c| ≤ Real.log b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b := by
  dsimp only
  have hc := InverseClippingProfiles.retained_clipped_column w Z N q a b hZ hq ha hb hw hret
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.1⟩
  rw [abs_of_nonneg (Real.log_nonneg hc.1)]
  exact Real.log_le_log (zero_lt_one.trans_le hc.1) hc.2.1

theorem first_second_tower_uniform
    (W₁ W₂ : ℝ → ℂ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀)
    (hsW₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ₁ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (MV : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hMV : ∀ i, 0 ≤ MV i) (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ₂ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A₁ A₂ J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    let outer := firstRootSchwartz V hV hVS
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ₁ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity outer b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ₂ (fun i y => U i (y+ρ i)) R₂ y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤ C := by
  dsimp only
  obtain ⟨C₂,hC₂,hsecond⟩ := second_profile_tower_uniform (ι := Fin 9)
    U g₁ g₂ Φ₂ M B m₁ m₂ b hM hB hU h₁ h₂ A₂ J
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a₀ b₀ ha₀ hsW₁ hsW₂ hW₁ hW₂ Φ₁ V MV hV hVS hMV hVbox A₁ (requiredOuterOrder J)
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,_,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,hc₃⟩ := hsecond R₂ hR₂
  refine ⟨b₃,c₃,he₁,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hc₃ ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have ht := h.2 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
  refine ⟨h.1,ht.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
  have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
  calc
    _ = (1+R₁)^A₁ * ((1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
            (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
            (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
            c₃ ρ c₁ c₂ L z‖)) := by ring
    _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9), ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity (firstRootSchwartz V hV hVS) b₁ b₂ b₃ p‖)) := hh
    _ ≤ C₂*C₁ := by
      simpa only [ambientWeight, tripleHeight, coordinateHeight, mul_assoc,
        mul_left_comm, mul_comm] using hh'

end SevenEighths.InverseSecondProfileUniform

end

end OAI
