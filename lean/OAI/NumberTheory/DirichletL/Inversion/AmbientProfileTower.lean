import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
import OAI.NumberTheory.DirichletL.Descent.WindowFourier
import OAI.NumberTheory.DirichletL.Descent.DescentHeight
import OAI.NumberTheory.DirichletL.Descent.FullProfile

namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

theorem frequencyTwist_fourier_joint_stronglyMeasurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : ℝ × ℝ => (𝓕 (frequencyTwist g p.1)) p.2) := by
  have hf : StronglyMeasurable
      (fun p : ℝ × ℝ => frequencyTwist g p.1 p.2) := by
    simp only [frequencyTwist_apply]
    apply Continuous.stronglyMeasurable
    unfold logPhase
    fun_prop
  exact InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun θ => (frequencyTwist g θ : ℝ → ℂ)) hf

theorem logSource_fourier_joint_stronglyMeasurable
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      (𝓕 (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) p.1)) p.2) :=
  frequencyTwist_fourier_joint_stronglyMeasurable _

theorem twistedTriple_joint_stronglyMeasurable (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Frequency =>
      tripleCoefficient (𝓕 (frequencyTwist g₁ p.1.1))
        (𝓕 (frequencyTwist g₂ p.1.2)) b₃ p.2) := by
  unfold tripleCoefficient
  exact ((frequencyTwist_fourier_joint_stronglyMeasurable g₁).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).mul
      (((frequencyTwist_fourier_joint_stronglyMeasurable g₂).comp_measurable
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))).mul
      (b₃.continuous.stronglyMeasurable.comp_measurable
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) : ℝ :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

theorem ambientWeight_eq_pow {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg p.1.1]))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.1])))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.2])))
    (Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

theorem ambientWeight_add {ι : Type*} [Fintype ι] (J K : ℕ) (p : Ambient ι) :
    ambientWeight (J + K) p = ambientWeight J p * ambientWeight K p := by
  rw [ambientWeight_eq_pow (J+K), ambientWeight_eq_pow J, ambientWeight_eq_pow K, pow_add]

def inheritedLeft {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

private theorem coordinate_factor_le {ι : Type*} [Fintype ι]
    (i : ι) (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

theorem inheritedLeft_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  simpa [inheritedLeft, ambientWeight, mul_comm, mul_left_comm, mul_assoc] using h

theorem inherited_pair_weight_bound {ι : Type*} [Fintype ι]
    (i j : ι) (J K : ℕ) (p : Ambient ι) :
    ambientWeight J p * ((1 + ‖inheritedLeft i p‖)^K *
      (1 + ‖inheritedRight j p‖)^K) ≤ ambientWeight (J + 2*K) p := by
  have h₁ := pow_le_pow_left₀ (by positivity) (inheritedLeft_bound i p) K
  have h₂ := pow_le_pow_left₀ (by positivity) (inheritedRight_bound j p) K
  have hh := mul_le_mul h₁ h₂ (by positivity)
    (pow_nonneg (le_trans zero_le_one (ambientWeight_one_le 1 p)) K)
  rw [← pow_add] at hh
  rw [ambientWeight_add, ambientWeight_eq_pow (2*K)]
  exact mul_le_mul_of_nonneg_left (by simpa [two_mul] using hh)
    (le_trans zero_le_one (ambientWeight_one_le J p))

theorem ambientWeight_continuous {ι : Type*} [Fintype ι] (J : ℕ) :
    Continuous (ambientWeight (ι := ι) J) := by
  unfold ambientWeight
  fun_prop

theorem inheritedLeft_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedLeft i) := by unfold inheritedLeft; fun_prop

theorem inheritedRight_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedRight i) := by unfold inheritedRight; fun_prop

private theorem inheritedParameter_measurable {ι κ : Type*} (i j : ι) :
    Measurable (fun z : Ambient ι × Ambient κ =>
      ((inheritedLeft i z.1,inheritedRight j z.1),z.2)) := by
  unfold inheritedLeft inheritedRight
  fun_prop

private theorem conditional_tower_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    Integrable (fun z : Ambient ι × Ambient κ =>
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) := by
  let f : Ambient ι × Ambient κ → ℝ := fun z =>
    ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖
  have hf_nonneg (z) : 0 ≤ f z := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg
      (le_trans zero_le_one (ambientWeight_one_le J z.1))
      (le_trans zero_le_one (ambientWeight_one_le J z.2))) (norm_nonneg _)
  have hsm : StronglyMeasurable f :=
    (((ambientWeight_continuous J).comp continuous_fst).stronglyMeasurable.mul
      ((ambientWeight_continuous J).comp continuous_snd).stronglyMeasurable).mul
        ((hB.comp_measurable measurable_fst).mul hD).norm
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => by
      convert (hi p).const_mul (ambientWeight J p * ‖B p‖) using 1
      funext q; dsimp only [f]; rw [norm_mul]; ring)
  · apply (houter.const_mul C).mono' (hsm.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards with p
    have he : (∫ q, ‖f (p,q)‖) =
        ambientWeight J p * ‖B p‖ * (∫ q, ambientWeight J q * ‖D p q‖) := by
      simp_rw [Real.norm_of_nonneg (hf_nonneg _)]
      have heq (q) : f (p,q) =
          (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
        dsimp only [f]; rw [norm_mul]; ring
      simp_rw [heq]
      exact integral_const_mul _ _
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
    calc
      _ ≤ ambientWeight J p * ‖B p‖ *
          (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
        mul_le_mul_of_nonneg_left (hb p)
          (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
      _ = (C * ‖B p‖) * (ambientWeight J p *
          ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
      _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
        mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
          (mul_nonneg hC (norm_nonneg _))
      _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

private theorem conditional_tower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    (∫ z : Ambient ι × Ambient κ,
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) ≤
      C * (∫ p, ambientWeight (J+2*K) p * ‖B p‖) := by
  have hprod := conditional_tower_integrable i j J K C hC B hB D hD hi hb houter
  rw [Measure.volume_eq_prod, integral_prod _ hprod, ← integral_const_mul]
  apply integral_mono hprod.integral_prod_left (houter.const_mul C)
  intro p
  have he (q) : ambientWeight J p * ambientWeight J q * ‖B p * D p q‖ =
      (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
    rw [norm_mul]; ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ ambientWeight J p * ‖B p‖ *
        (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
      mul_le_mul_of_nonneg_left (hb p)
        (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
    _ = (C * ‖B p‖) * (ambientWeight J p *
        ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
    _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
      mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
        (mul_nonneg hC (norm_nonneg _))
    _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

theorem integrable_density_test {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    Integrable (fun z => D z * F z) := by
  apply hi.mono' (hD.mul hF).aestronglyMeasurable
  filter_upwards with z
  change ‖D z * F z‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hFbound z) (norm_nonneg _)

theorem density_test_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, D z * F z) = ∫ p, ∫ q, D (p,q) * F (p,q) := by
  have h := integrable_density_test D F hD hF J hi hFbound
  simpa only [Measure.volume_eq_prod] using integral_prod (fun z => D z * F z) h

def twistedFullDensity {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι) : ℂ :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

theorem fullProfileDensity_continuous {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Continuous (fullProfileDensity g b₁ b₂ b₃) := by
  unfold fullProfileDensity tripleCoefficient coordinateDensity
  fun_prop

theorem twistedFullDensity_joint_stronglyMeasurable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Ambient ι =>
      twistedFullDensity g g₁ g₂ b₃ p.1 p.2) := by
  unfold twistedFullDensity fullProfileDensity
  apply StronglyMeasurable.mul
  · have hm : Measurable (fun p : (ℝ × ℝ) × Ambient ι => (p.1,p.2.1)) := by fun_prop
    simpa only [Function.comp_def] using
      (twistedTriple_joint_stronglyMeasurable g₁ g₂ b₃).comp_measurable hm
  · apply Continuous.stronglyMeasurable
    unfold coordinateDensity
    fun_prop

theorem fullProfileDensity_weighted_integrable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Ambient ι =>
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [ambientWeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Ambient ι, ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency,
        ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖) := by
  have he (p : Ambient ι) :
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
      (((1+‖p.1.1‖)^J * (1+‖p.1.2.1‖)^J * (1+‖p.1.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
      ((∏ i, (1+‖p.2 i‖)^J) * ‖coordinateDensity g p.2‖) := by
    simp only [ambientWeight, fullProfileDensity, norm_mul]; ring
  simp_rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun t : Frequency => ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
      ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖)

def towerMomentOrder (J : ℕ) : ℕ := J + 2*(J + (volume : Measure ℝ).integrablePower)

theorem twistedFullDensity_moment {ι : Type*} [Fintype ι]
    (J : ℕ) (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ × ℝ,
      (∫ p : Ambient ι, ambientWeight J p * ‖twistedFullDensity g g₁ g₂ b₃ θ p‖) ≤
      C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  let M := ∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  let B := ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁*C₂*B*M, by positivity, ?_⟩
  intro θ
  unfold twistedFullDensity
  rw [fullProfileDensity_weighted_integral,
    tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (h₁ θ.1) (h₂ θ.2)
    (integral_nonneg (fun _ => by positivity)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hB) hM
  convert hh' using 1
  ring

def towerDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (z : Ambient ι × Ambient κ) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    twistedFullDensity inner g₁ g₂ c₃
      (inheritedLeft i z.1, inheritedRight j z.1) z.2

theorem towerDensity_joint_stronglyMeasurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃) := by
  unfold towerDensity
  apply StronglyMeasurable.mul
  · exact ((fullProfileDensity_continuous outer b₁ b₂ b₃).comp continuous_fst).stronglyMeasurable
  · simpa only [Function.comp_def] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)

theorem towerDensity_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ℕ) (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      Integrable (fun z : Ambient ι × Ambient κ =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
      (∫ z : Ambient ι × Ambient κ,
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
        C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
          ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  obtain ⟨C,hC,hb⟩ := twistedFullDensity_moment J inner g₁ g₂ c₃
  refine ⟨C,hC,?_⟩
  intro i j outer b₁ b₂ b₃
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p, inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  exact ⟨conditional_tower_integrable i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout,
    conditional_tower_bound i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout⟩

theorem towerDensity_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (F : Ambient ι × Ambient κ → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z * F z) =
      ∫ p, ∫ q, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ (p,q) * F (p,q) := by
  obtain ⟨C,hC,h⟩ := towerDensity_weighted (ι := ι) J inner g₁ g₂ c₃
  exact density_test_fubini _ F
    (towerDensity_joint_stronglyMeasurable i j outer b₁ b₂ b₃ inner g₁ g₂ c₃)
    hF J (h i j outer b₁ b₂ b₃).1 hFbound

theorem first_inherited_left_eq (p : Ambient (Fin 9)) :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq (p : Ambient (Fin 9)) :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem second_inherited_left_eq (p : Ambient (Fin 6)) :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq (p : Ambient (Fin 6)) :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem twistedFullDensity_uniform_separation {κ : Type*} [Fintype κ]
    (g : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, g i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, g i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity g g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ θ : ℝ × ℝ,
        (1+R)^A * (∫ p : Ambient κ,
          ambientWeight J p * ‖twistedFullDensity g g₁ g₂ c₃ θ p‖) ≤
        C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower))) := by
  obtain ⟨C,hC,hs⟩ := twisted_descent_profile_separation
    g₁ g₂ Φ (fun i => g i) a₁ a₂ ak M hM hbox A J
  let G := ∫ u : κ → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  have hG : 0 ≤ G := integral_nonneg (fun _ => by positivity)
  refine ⟨C*G,mul_nonneg hC hG,?_⟩
  intro R hR
  obtain ⟨c₃,hc⟩ := hs R hR
  refine ⟨c₃,?_,?_⟩
  · intro θ y
    rw [(hc θ.1 θ.2).1 y]
    exact profile_integral_coordinate_absorption g
      (𝓕 (frequencyTwist g₁ θ.1)) (𝓕 (frequencyTwist g₂ θ.2)) c₃ a₁ a₂ ak y
  · intro θ
    unfold twistedFullDensity
    rw [fullProfileDensity_weighted_integral]
    have hh := mul_le_mul_of_nonneg_right (hc θ.1 θ.2).2.2 hG
    convert hh using 1 <;> ring

theorem fullProfile_tower_uniform {ι κ : Type*} [Fintype ι] [Fintype κ]
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, inner i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, inner i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity inner g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient κ =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient κ,
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  obtain ⟨C,hC,hs⟩ := twistedFullDensity_uniform_separation inner g₁ g₂ Φ a₁ a₂ ak M hM hbox A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,he,hb⟩ := hs R hR
  refine ⟨c₃,he,?_⟩
  intro i j outer b₁ b₂ b₃
  have hRpow : 0 < (1+R)^A := pow_pos (by linarith) A
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p,inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hb' (p : Ambient ι) : (∫ q, ambientWeight J q * ‖D p q‖) ≤
      (C/(1+R)^A) * ((1+‖inheritedLeft i p‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖inheritedRight j p‖)^(J + (volume : Measure ℝ).integrablePower)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hRpow).mpr
    simpa only [mul_comm] using hb (inheritedLeft i p,inheritedRight j p)
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  have hi' := conditional_tower_integrable i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  have hb'' := conditional_tower_bound i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  refine ⟨hi',?_⟩
  have hh := mul_le_mul_of_nonneg_left hb'' hRpow.le
  have hcancel (x : ℝ) : (1+R)^A * (C/(1+R)^A*x) = C*x := by
    field_simp [ne_of_gt hRpow]
  rw [hcancel] at hh
  simpa only [towerDensity, D, towerMomentOrder] using hh

def twistedPositiveSource (W : ℝ → ℂ) (θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W x

theorem first_second_profile_tower
    (W₁ W₂ U₁ U₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a b) (hsW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hsU₁ : Function.support U₁ ⊆ Set.Icc a b) (hsU₂ : Function.support U₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (T : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hT : ∀ i, ContDiff ℝ ∞ (T i)) (hTS : ∀ i, HasCompactSupport (T i))
    (MV : Fin 9 → ℝ) (MT : Fin 6 → ℝ)
    (hMV : ∀ i, 0 ≤ MV i) (hMT : ∀ i, 0 ≤ MT i)
    (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (hTbox : ∀ i y, T i y ≠ 0 → |y| ≤ MT i) (A₁ A₂ J : ℕ) :
    let G := firstRootSchwartz V hV hVS
    let H := secondRootSchwartz T hT hTS
    let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
    let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity G b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      (∀ (θ : ℝ × ℝ) (y : Fin 6 → ℝ),
        secondPoissonProfile (twistedPositiveSource U₁ θ.1)
          (twistedPositiveSource U₂ θ.2) Ψ T R₂ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          twistedFullDensity H g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃) u) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ *
        (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ≤ C := by
  dsimp only
  let G := firstRootSchwartz V hV hVS
  let H := secondRootSchwartz T hT hTS
  let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
  let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a b ha hsW₁ hsW₂ hW₁ hW₂ Φ V MV hV hVS hMV hVbox A₁ (towerMomentOrder J)
  have hbox : ∀ i y, H i y ≠ 0 → |y| ≤ MT i := by
    intro i y hy
    change secondRootWindows T i y ≠ 0 at hy
    fin_cases i <;> apply hTbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₂,hC₂,hsecond⟩ := fullProfile_tower_uniform (ι := Fin 9)
    H g₁ g₂ Ψ secondLeftSlope secondRightSlope secondKernelSlope MT hMT hbox A₂ J
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,hi₁,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,he₂,htower⟩ := hsecond R₂ hR₂
  have ht := htower 7 8 G b₁ b₂ b₃
  refine ⟨b₃,c₃,he₁,?_,ht.1,?_⟩
  · intro θ y
    simpa only [secondPoissonProfile, twistedPositiveSource, Real.log_exp,
      frequencyTwist_apply, g₁, g₂, CubicReflectionKernel.logSchwartz_apply,
      H, secondRootSchwartz, rootSchwartz_apply] using he₂ θ y
  · have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
    have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
    calc
      _ = (1+R₁)^A₁ * ((1+R₂)^A₂ *
          (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
            ambientWeight J z.1 * ambientWeight J z.2 *
              ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖)) := by ring
      _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9),
          ambientWeight (towerMomentOrder J) p * ‖fullProfileDensity G b₁ b₂ b₃ p‖)) := hh
      _ ≤ C₂*C₁ := by
        simpa only [ambientWeight, tripleHeight, coordinateHeight, G, mul_assoc,
          mul_left_comm, mul_comm] using hh'

end
end SevenEighths.InverseAmbientProfileTower

end OAI
