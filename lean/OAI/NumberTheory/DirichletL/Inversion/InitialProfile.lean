import OAI.NumberTheory.DirichletL.Inversion.ClippingProfiles
import OAI.NumberTheory.DirichletL.Descent.SecondFreshMeasure
import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = logPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  logPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => logPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_joint_measurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => sourceDensity g p.1.1 p.1.2 p.2) := by
  unfold sourceDensity logPhase
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · exact Complex.continuous_exp.measurable.comp (by fun_prop)
  · exact (𝓕 g : 𝓢(ℝ, ℂ)).continuous.measurable.comp (by fun_prop)

theorem sourceDensity_norm (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    ‖sourceDensity g c θ t‖ = ‖(𝓕 g) (t-θ)‖ := by
  simp [sourceDensity, logPhase_norm]

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W (c*x)

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CubicReflectionKernel.logSchwartz_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

def rootExponent (y : Fin 6 → ℝ) : ℝ := -y 1-y 2-(y 4+y 5)/2

theorem root_coupled_identity (y : Fin 6 → ℝ) :
    rootExponent y = -y 1+y 0-((y 0+y 2+y 4)+(y 0+y 2+y 5))/2 := by
  unfold rootExponent
  ring

theorem root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (hd : |y 1| ≤ L) (hC : |y 0| ≤ L)
    (hc₁ : |y 0+y 2+y 4| ≤ L) (hc₂ : |y 0+y 2+y 5| ≤ L) :
    rootExponent y ≤ 3*L := by
  rw [root_coupled_identity]
  have hd' := (abs_le.mp hd).1
  have hC' := (abs_le.mp hC).2
  have h1 := (abs_le.mp hc₁).1
  have h2 := (abs_le.mp hc₂).1
  linarith

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

theorem normalizedProfile_exact (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    normalizedProfile W₁ W₂ Φ V R L y =
      (Real.exp (rootExponent y-3*L) : ℂ) * (∏ i, V i (y i)) *
      W₁ (Real.exp (y 0+y 2+y 4)) * W₂ (Real.exp (y 0+y 2+y 5)) *
      paperRadialFourier Φ (R*Real.exp (y 3-y 1-2*y 2-y 4-y 5)) := by
  unfold normalizedProfile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  have hleft : (∑ i, secondLeftSlope i*y i) = y 0+y 2+y 4 := by
    simp [secondLeftSlope, Fin.sum_univ_succ]
    ring
  have hright : (∑ i, secondRightSlope i*y i) = y 0+y 2+y 5 := by
    simp [secondRightSlope, Fin.sum_univ_succ]
    ring
  have hker : (∑ i, secondKernelSlope i*y i) = y 3-y 1-2*y 2-y 4-y 5 := by
    simp [secondKernelSlope, Fin.sum_univ_succ]
    ring
  rw [hleft, hright, hker]
  change (Real.exp (-3*L) : ℂ) * (((Real.exp (rootExponent y) : ℂ)*_)*_*_*_) = _
  rw [show Real.exp (rootExponent y-3*L) = Real.exp (-3*L)*Real.exp (rootExponent y) by
    rw [← Real.exp_add]; congr 1; ring, Complex.ofReal_mul]
  ring

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem familyDensity_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) :
    familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p =
      (Real.exp (-3*L) : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 *
          (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) * coordinateDensity g p.2 := by
  simp only [familyDensity, fullProfileDensity, tripleCoefficient, fourier_clippedTwist]
  ring

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

theorem sourceDensity_moment_seminorm (g : 𝓢(ℝ, ℂ)) (M b : ℝ)
    (hM : 0 ≤ M) (hb : 1 ≤ b) (hg : Function.support g ⊆ Set.Icc (-M) M)
    (J : ℕ) {c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ b) (θ : ℝ) :
    (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
      InverseClippingProfiles.windowMomentConstant g M (Real.log b) 0 J *
        (1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hlog : |Real.log c| ≤ Real.log b * 1 := by
    rw [mul_one, abs_of_nonneg (Real.log_nonneg hc)]
    exact Real.log_le_log hc0 hcb
  have he : clippedTwist g c θ = frequencyTwist
      (InverseClippingProfiles.rootSchwartz g M (Real.log b) 1 (Real.log c) 0 0
        zero_lt_one hlog hg) θ := by
    ext y
    simp [InverseClippingProfiles.rootSchwartz_apply,
      InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]
  have hm := InverseClippingProfiles.rooted_twist_fourier_moment g M (Real.log b)
    1 (Real.log c) 0 0 θ hM (Real.log_nonneg hb) le_rfl hlog hg (by simp) J
  simp_rw [← fourier_clippedTwist, he]
  simpa only [InverseClippingProfiles.windowMomentConstant, one_pow, mul_one] using hm

theorem clippedSource_conjugate (W : ℝ → ℂ) (c θ x : ℝ) :
    star (clippedSource W c θ x) = clippedSource (fun x => star (W x)) c (-θ) x := by
  simp only [clippedSource, star_mul, SecondPassIntegration.logPhase_conjugate]
  ring

theorem familyDensity_joint_measurable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) (L : ℝ) :
    StronglyMeasurable (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (Frequency × (Fin 6 → ℝ)) =>
      familyDensity g g₁ g₂ b₃ z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 L z.2) := by
  simp_rw [familyDensity_formula]
  apply Measurable.stronglyMeasurable
  unfold sourceDensity coordinateDensity logPhase
  have h1 : Measurable ((𝓕 g₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 : Measurable ((𝓕 g₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 : Measurable (b₃ : ℝ → ℂ) := b₃.continuous.measurable
  have hu (i : Fin 6) : Measurable ((𝓕 (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have hexp : Measurable Complex.exp := Complex.continuous_exp.measurable
  fun_prop

theorem fresh_cutoff_one (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (_ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hω : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (hs : W (c*(u*v*x)) ≠ 0) : w x = 1 := by
  have hu0 : 0 < u := hA₀.trans_le hu.1
  have hv0 : 0 < v := hA₂.trans_le hv.1
  have hB₀ : 0 < B₀ := hu0.trans_le hu.2
  have hB₂ : 0 < B₂ := hv0.trans_le hv.2
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs' := hW hs
  have hlo : A₀*A₂ ≤ c*(u*v) := by
    have hprod := mul_le_mul hu.1 hv.1 hA₂.le hu0.le
    exact hprod.trans (le_mul_of_one_le_left (mul_nonneg hu0.le hv0.le) hc)
  have hhi : c*(u*v) ≤ bclip*B₀*B₂ := by
    have hprod := mul_le_mul hu.2 hv.2 hv0.le hB₀.le
    exact (mul_le_mul hcb hprod (mul_nonneg hu0.le hv0.le)
      (zero_lt_one.trans_le hclip).le).trans_eq (by ring)
  apply hω x
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < bclip*B₀*B₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hhi hx.le
    nlinarith [hs'.1]
  · apply (le_div_iff₀ (mul_pos hA₀ hA₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hx.le
    nlinarith [hs'.2]

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
  ring

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
        (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
    (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

theorem fresh_cutoff_one_clippedSource (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hw : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (θ : ℝ) (hs : clippedSource W c θ (u*v*x) ≠ 0) : w x = 1 := by
  exact fresh_cutoff_one W w a b bclip A₀ B₀ A₂ B₂ ha hA₀ hA₂ hclip hW hw
    hc hcb hu hv hx (mul_ne_zero_iff.mp hs).2

theorem clipped_column_ratio {Z : ℝ} (hZ : 0 < Z) (N q : ℝ) :
    q / Z^N = Z^(max 0 N-N) * (q / Z^(max 0 N)) := by
  rw [Real.rpow_sub hZ]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ N),
    ne_of_gt (Real.rpow_pos_of_pos hZ (max 0 N))]

theorem clipped_column_source_identity (w : ℝ → ℂ) {Z q : ℝ}
    (hZ : 0 < Z) (hq : 0 < q) (N θ : ℝ) :
    logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
      logPhase θ (Real.log (Z^(max 0 N-N))) *
        clippedSource w (Z^(max 0 N-N)) θ (q/Z^(max 0 N)) := by
  rw [clipped_column_ratio hZ N q]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ _))
    (ne_of_gt (div_pos hq (Real.rpow_pos_of_pos hZ _))), logPhase_add]
  unfold clippedSource
  ring

theorem retained_initial_clipping (w : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hs : ContDiff ℝ ∞ w) (J : ℕ) :
    let g := CubicReflectionKernel.logSchwartz w a b ha hw hs
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z N q : ℝ, 1 < Z → 1 ≤ q → w (q/Z^N) ≠ 0 →
      let c := Z^(max 0 N-N)
      1 ≤ c ∧ c ≤ b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
      (∀ θ : ℝ, logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
        logPhase θ (Real.log c) * clippedSource w c θ (q/Z^(max 0 N))) ∧
      (∀ θ : ℝ, Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
          C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := sourceDensity_moment_uniform
    (CubicReflectionKernel.logSchwartz w a b ha hw hs) J
  refine ⟨C, hC, ?_⟩
  intro Z N q hZ hq hwitness
  obtain ⟨hc, hcb, hsupport, _⟩ := InverseClippingProfiles.retained_clipped_column
    w Z N q a b hZ hq ha hb hw hwitness
  refine ⟨hc, hcb, hsupport, ?_, fun θ => hbound _ θ⟩
  exact fun θ => clipped_column_source_identity w (zero_lt_one.trans hZ)
    (zero_lt_one.trans_le hq) N θ

end SevenEighths.InverseInitialProfile

end

end OAI
