import OAI.MathematicalPhysics.Boltzmann.Branching.Moments
import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Distributions.Gaussian.Real

namespace OAI

section

/-! # Pointwise Gaussian norm bounds for the fixed-cutoff equation

Detailed balance removes the output Gaussian from the gain. These estimates
are for the actual collision integral, with no published-input hypothesis.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetGaussianMoments

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X : Type*} [MeasurableSpace X]

def mass (β : ℝ) : ℝ := ∫ v, JetGaussianMoments.kernel β v

def gainConstant (β b : ℝ) : ℝ := 4 * Real.pi * b * mass β

def lossConstant (β b : ℝ) : ℝ := 2 * Real.pi * b * mass β

theorem constants_nonneg {b : ℝ} (hb : 0 ≤ b) (β : ℝ) :
    0 ≤ gainConstant β b ∧ 0 ≤ lossConstant β b := by
  have hm : 0 ≤ mass β := integral_nonneg (fun _ => (Real.exp_pos _).le)
  unfold gainConstant lossConstant
  constructor <;> positivity

def integrand (β b : ℝ) (f g : X × Velocity → ℝ)
    (p : X × Velocity) (w : Velocity × Sphere) : ℝ :=
  CollisionCutoff.kernel b p.2 w.1 w.2 * JetGaussianMoments.kernel β w.1 *
    f (p.1, scatterLeft p.2 w.1 w.2) * g (p.1, scatterRight p.2 w.1 w.2)

def gain (β b : ℝ) (f g : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ w, integrand β b f g p w ∂(volume.prod sphereArea)

def frequency (β b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  KineticCollisionNullSets.frequency b (fun q => JetGaussianMoments.kernel β q.2 * f q) p

theorem kernel_le {b : ℝ} (hb : 0 ≤ b) (v w : Velocity) (ω : Sphere) :
    CollisionCutoff.kernel b v w ω ≤ b := by
  unfold CollisionCutoff.kernel
  split_ifs with h
  · have hi : collisionKernel v w ω ≤ ‖v - w‖ := by
      simpa only [collisionKernel, normalComponent,
        mem_sphere_zero_iff_norm.mp ω.property, mul_one] using
        abs_real_inner_le_norm (v - w) (ω : Velocity)
    exact hi.trans h.le
  · exact hb

theorem measurable_integrand {f g : X × Velocity → ℝ}
    (hf : Measurable f) (hg : Measurable g) (β b : ℝ) :
    Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => integrand β b f g p.1 p.2) := by
  have hL := hf.comp (show Measurable (KineticCollisionNullSets.left (X := X)) by
    unfold KineticCollisionNullSets.left scatterLeft normalComponent; fun_prop)
  have hR := hg.comp (show Measurable (KineticCollisionNullSets.right (X := X)) by
    unfold KineticCollisionNullSets.right scatterRight normalComponent; fun_prop)
  have hk : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b p.1.2 p.2.1 p.2.2) := by
    unfold CollisionCutoff.kernel
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by unfold collisionKernel normalComponent; fun_prop) measurable_const
  exact ((hk.mul (by unfold JetGaussianMoments.kernel; fun_prop)).mul hL).mul hR

theorem measurable_gain {f g : X × Velocity → ℝ}
    (hf : Measurable f) (hg : Measurable g) (β b : ℝ) : Measurable (gain β b f g) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  exact (measurable_integrand hf hg β b).stronglyMeasurable.integral_prod_right.measurable

omit [MeasurableSpace X] in
theorem integrand_bound {b A B : ℝ} (hb : 0 ≤ b) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    {f g : X × Velocity → ℝ} (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (β : ℝ) (p : X × Velocity) (w : Velocity × Sphere) :
    |integrand β b f g p w| ≤ (b * A * B) * JetGaussianMoments.kernel β w.1 := by
  have hw : 0 ≤ JetGaussianMoments.kernel β w.1 := (Real.exp_pos _).le
  unfold integrand
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _),
    abs_of_nonneg hw]
  calc
    _ ≤ b * JetGaussianMoments.kernel β w.1 * A * B := by
      gcongr
      · exact kernel_le hb _ _ _
      · exact hf _
      · exact hg _
    _ = _ := by ring

theorem majorant_integrable {β : ℝ} (hβ : 0 < β) (C : ℝ) :
    Integrable (fun w : Velocity × Sphere => C * JetGaussianMoments.kernel β w.1)
      (volume.prod sphereArea) := by
  simpa only [mul_one] using ((kernel_integrable hβ).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : Sphere => (1 : ℝ)) sphereArea)).const_mul C

theorem majorant_integral (β C : ℝ) :
    (∫ w : Velocity × Sphere, C * JetGaussianMoments.kernel β w.1 ∂(volume.prod sphereArea)) =
      C * (mass β * (4 * Real.pi)) := by
  rw [integral_const_mul]
  have he := integral_prod_mul (JetGaussianMoments.kernel β) (fun _ : Sphere => (1 : ℝ))
    (μ := (volume : Measure Velocity)) (ν := sphereArea)
  simpa only [mul_one, integral_const, smul_eq_mul, mul_one, sphereArea_real_univ, mass] using
    congrArg (fun z : ℝ => C * z) he

theorem integrable_gain {β b A B : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B) (p : X × Velocity) :
    Integrable (integrand β b f g p) (volume.prod sphereArea) := by
  apply (majorant_integrable hβ (b * A * B)).mono'
  · exact ((measurable_integrand hfm hgm β b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using integrand_bound hb hA hB hf hg β p w)

omit [MeasurableSpace X] in
theorem gain_bound {β b A B : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f g : X × Velocity → ℝ} (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (p : X × Velocity) : |gain β b f g p| ≤ gainConstant β b * A * B := by
  have h := norm_integral_le_of_norm_le (f := integrand β b f g p) (majorant_integrable hβ (b * A * B))
    (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using integrand_bound hb hA hB hf hg β p w))
  rw [majorant_integral] at h
  simpa only [gain, Real.norm_eq_abs] using h.trans_eq (by unfold gainConstant; ring)

omit [MeasurableSpace X] in
theorem gain_nonneg {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (β b : ℝ) (p : X × Velocity) : 0 ≤ gain β b f g p := by
  apply integral_nonneg
  intro w
  exact mul_nonneg (mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
    (Real.exp_pos _).le) (hf _)) (hg _)

omit [MeasurableSpace X] in
theorem gain_eq_actual (β b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    JetGaussianMoments.kernel β p.2 * gain β b f f p =
      CollisionCutoff.gain b (fun v => JetGaussianMoments.kernel β v * f (p.1, v)) p.2 := by
  rw [gain, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he := gaussian_detailed_balance 1 β 0 p.2 w.1 w.2 (mem_sphere_zero_iff_norm.mp w.2.property)
  simp only [gaussian, sub_zero, one_mul] at he
  change Real.exp (-β * ‖_‖ ^ 2) * Real.exp (-β * ‖_‖ ^ 2) = _ at he
  unfold integrand CollisionCutoff.integrand JetGaussianMoments.kernel
  calc
    _ = CollisionCutoff.kernel b p.2 w.1 w.2 *
        (Real.exp (-β * ‖p.2‖ ^ 2) * Real.exp (-β * ‖w.1‖ ^ 2)) *
        f (p.1, scatterLeft p.2 w.1 w.2) * f (p.1, scatterRight p.2 w.1 w.2) := by ring
    _ = CollisionCutoff.kernel b p.2 w.1 w.2 *
        (Real.exp (-β * ‖scatterLeft p.2 w.1 w.2‖ ^ 2) *
          Real.exp (-β * ‖scatterRight p.2 w.1 w.2‖ ^ 2)) *
        f (p.1, scatterLeft p.2 w.1 w.2) * f (p.1, scatterRight p.2 w.1 w.2) := by rw [he]
    _ = _ := by ring

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-! # Stability and positivity of the Gaussian-normalized cutoff source -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetGaussianMoments

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X : Type*} [MeasurableSpace X]

private theorem product_difference {a b c d A B D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (ha : |a| ≤ A) (hd : |d| ≤ B)
    (hac : |a - c| ≤ D) (hbd : |b - d| ≤ D) : |a * b - c * d| ≤ D * (A + B) := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a| * |b - d| + |a - c| * |d| := by simpa only [abs_mul] using abs_add_le (a * (b - d)) ((a - c) * d)
    _ ≤ A * D + D * B := add_le_add
      (mul_le_mul ha hbd (abs_nonneg _) hA) (mul_le_mul hac hd (abs_nonneg _) hD)
    _ = _ := by ring

theorem gain_difference {β b A B D : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (hfg : ∀ p, |f p - g p| ≤ D) (p : X × Velocity) :
    |gain β b f f p - gain β b g g p| ≤ gainConstant β b * D * (A + B) := by
  unfold gain
  rw [← integral_sub (integrable_gain hβ hb hA hA hfm hfm hf hf p)
    (integrable_gain hβ hb hB hB hgm hgm hg hg p)]
  have hp (w : Velocity × Sphere) :
      ‖integrand β b f f p w - integrand β b g g p w‖ ≤
        (b * (D * (A + B))) * JetGaussianMoments.kernel β w.1 := by
    have hw : 0 ≤ JetGaussianMoments.kernel β w.1 := (Real.exp_pos _).le
    have hprod := product_difference hA hD (hf (p.1, scatterLeft p.2 w.1 w.2))
      (hg (p.1, scatterRight p.2 w.1 w.2))
      (hfg (p.1, scatterLeft p.2 w.1 w.2)) (hfg (p.1, scatterRight p.2 w.1 w.2))
    rw [Real.norm_eq_abs]
    unfold integrand
    rw [show CollisionCutoff.kernel b p.2 w.1 w.2 * JetGaussianMoments.kernel β w.1 *
        f (p.1, scatterLeft p.2 w.1 w.2) * f (p.1, scatterRight p.2 w.1 w.2) -
        CollisionCutoff.kernel b p.2 w.1 w.2 * JetGaussianMoments.kernel β w.1 *
        g (p.1, scatterLeft p.2 w.1 w.2) * g (p.1, scatterRight p.2 w.1 w.2) =
        (CollisionCutoff.kernel b p.2 w.1 w.2 * JetGaussianMoments.kernel β w.1) *
        (f (p.1, scatterLeft p.2 w.1 w.2) * f (p.1, scatterRight p.2 w.1 w.2) -
        g (p.1, scatterLeft p.2 w.1 w.2) * g (p.1, scatterRight p.2 w.1 w.2)) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) hw)]
    calc
      _ ≤ (b * JetGaussianMoments.kernel β w.1) * (D * (A + B)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (kernel_le hb _ _ _) hw) hprod (abs_nonneg _)
          (mul_nonneg hb hw)
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le (majorant_integrable hβ (b * (D * (A + B)))) (ae_of_all _ hp)
  rw [majorant_integral] at h
  simpa only [Real.norm_eq_abs] using h.trans_eq (by unfold gainConstant; ring)

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (β b : ℝ) :
    Measurable (frequency β b f) := by
  apply KineticCollisionNullSets.measurable_frequency
  have hk : Measurable (fun p : X × Velocity => JetGaussianMoments.kernel β p.2) := by
    unfold JetGaussianMoments.kernel
    fun_prop
  exact hk.mul hf

omit [MeasurableSpace X] in
theorem frequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (β b : ℝ) (p : X × Velocity) : 0 ≤ frequency β b f p := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg _ _ _)
    (mul_nonneg (Real.exp_pos _).le (hf _)))

omit [MeasurableSpace X] in
theorem frequency_bound {β b A : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hf : ∀ p, |f p| ≤ A) (p : X × Velocity) :
    |frequency β b f p| ≤ lossConstant β b * A := by
  have hp (w : Velocity) : ‖CollisionCutoff.rate b p.2 w *
      (JetGaussianMoments.kernel β w * f (p.1, w))‖ ≤
      (b * A) * JetGaussianMoments.kernel β w := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (CollisionCutoff.rate_nonneg _ _ _),
      abs_mul, abs_of_nonneg (show 0 ≤ JetGaussianMoments.kernel β w from (Real.exp_pos _).le)]
    calc
      _ ≤ b * (JetGaussianMoments.kernel β w * A) :=
        mul_le_mul (CollisionCutoff.rate_le hb _ _) (mul_le_mul_of_nonneg_left (hf _) (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) hb
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le ((kernel_integrable hβ).const_mul (b * A)) (ae_of_all _ hp)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  change |2 * Real.pi * _| ≤ _
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by unfold lossConstant mass; ring)

theorem frequency_difference {β b A B D : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (hfg : ∀ p, |f p - g p| ≤ D) (p : X × Velocity) :
    |frequency β b f p - frequency β b g p| ≤ lossConstant β b * D := by
  have hfi : Integrable (fun w => JetGaussianMoments.kernel β w * f (p.1, w)) := by
    apply ((kernel_integrable hβ).const_mul A).mono'
    · have hk : Measurable (JetGaussianMoments.kernel β) := by unfold JetGaussianMoments.kernel; fun_prop
      exact (hk.mul (hfm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    · filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ JetGaussianMoments.kernel β w from (Real.exp_pos _).le)]
      simpa only [mul_comm A, JetGaussianMoments.kernel] using mul_le_mul_of_nonneg_left (hf (p.1, w)) (Real.exp_pos _).le
  have hgi : Integrable (fun w => JetGaussianMoments.kernel β w * g (p.1, w)) := by
    apply ((kernel_integrable hβ).const_mul B).mono'
    · have hk : Measurable (JetGaussianMoments.kernel β) := by unfold JetGaussianMoments.kernel; fun_prop
      exact (hk.mul (hgm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    · filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ JetGaussianMoments.kernel β w from (Real.exp_pos _).le)]
      simpa only [mul_comm B, JetGaussianMoments.kernel] using mul_le_mul_of_nonneg_left (hg (p.1, w)) (Real.exp_pos _).le
  have he : frequency β b f p - frequency β b g p = frequency β b (fun p => f p - g p) p := by
    unfold frequency KineticCollisionNullSets.frequency CollisionCutoff.frequency
    rw [← mul_sub, ← integral_sub (CollisionCutoff.integrable_frequency hb hfi p.2)
      (CollisionCutoff.integrable_frequency hb hgi p.2)]
    congr 2
    funext w
    ring
  rw [he]
  exact frequency_bound hβ hb hfg p

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-! # The Maxwellian reference entropy

Finite weighted absolute entropy makes the relative-entropy integral genuine.
Its nonnegativity is proved, including the zero-density convention.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem log_maxwellian (v : Velocity) :
    Real.log (maxwellian v) = -(3 / 2 : ℝ) * Real.log (2 * Real.pi) - ‖v‖ ^ 2 / 2 := by
  have hp : 0 < (2 : ℝ) * Real.pi := by positivity
  rw [maxwellian, Real.log_mul (Real.rpow_pos_of_pos hp _).ne' (Real.exp_ne_zero _),
    Real.log_rpow hp, Real.log_exp]
  ring

theorem integrable_maxwellian : Integrable maxwellian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1 / 2 : ℂ)).re) 0 (0 : Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖ ^ 2 / 2)) := by
    convert! h using 1
    funext v
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  exact hg.const_mul _

theorem integrable_maxwellian_phase : Integrable (fun z : Phase => maxwellian z.2) :=
  integrable_maxwellian.comp_snd volume

theorem relativeEntropyDensity_eq {f : Density} {z : Phase} (hz : 0 ≤ f z) :
    f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2 =
      f z * Real.log (f z) + ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1) * f z +
        (1 / 2 : ℝ) * (‖z.2‖ ^ 2 * f z) + maxwellian z.2 := by
  rcases hz.eq_or_lt with hz | hz
  · simp [← hz]
  · rw [Real.log_div hz.ne' (maxwellian_pos _).ne', log_maxwellian]
    ring

theorem FiniteEntropyDatum.integrable_relativeEntropy {f : Density} (hf : FiniteEntropyDatum f) :
    Integrable (fun z => f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2) := by
  have h := ((hf.integrable_entropy.add
    (hf.integrable.const_mul ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1))).add
    (hf.integrable_energy.const_mul (1 / 2 : ℝ))).add integrable_maxwellian_phase
  apply h.congr
  filter_upwards [hf.1] with z hz
  exact (relativeEntropyDensity_eq hz).symm

/-- The scalar relative entropy is nonnegative at every nonnegative density value. -/
theorem relativeEntropyDensity_nonneg {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    0 ≤ a * Real.log (a / m) - a + m := by
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha, hm.le]
  · have h := Real.log_le_sub_one_of_pos (div_pos hm ha)
    have hlog : Real.log (m / a) = -Real.log (a / m) := by
      rw [Real.log_div hm.ne' ha.ne', Real.log_div ha.ne' hm.ne']
      ring
    rw [hlog] at h
    have hh := mul_le_mul_of_nonneg_left h ha.le
    have he : a * (m / a - 1) = m - a := by field_simp
    rw [he] at hh
    nlinarith only [hh]

theorem relativeEntropy_nonneg {f : Density} (hf : FiniteEntropyDatum f) :
    0 ≤ relativeEntropy f := by
  apply integral_nonneg_of_ae
  filter_upwards [hf.1] with z hz
  exact relativeEntropyDensity_nonneg hz (maxwellian_pos _)

end BoltzmannNonuniqueness

end

end

section

/-! # Colored and monotone-limit bounds for the cutoff Gaussian gain -/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X I : Type*} [MeasurableSpace X]

theorem gain_mono {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hfg : ∀ p, f p ≤ g p) (hg : ∀ p, g p ≤ R)
    (p : X × Velocity) : gain β b f f p ≤ gain β b g g p := by
  have hgn (p) : 0 ≤ g p := (hf p).trans (hfg p)
  have hfa (p) : |f p| ≤ R := by rw [abs_of_nonneg (hf p)]; exact (hfg p).trans (hg p)
  have hga (p) : |g p| ≤ R := by rw [abs_of_nonneg (hgn p)]; exact hg p
  apply integral_mono (integrable_gain hβ hb hR hR hfm hfm hfa hfa p)
    (integrable_gain hβ hb hR hR hgm hgm hga hga p)
  intro w
  unfold integrand
  have hk := mul_nonneg (CollisionCutoff.kernel_nonneg b p.2 w.1 w.2)
    (show 0 ≤ JetGaussianMoments.kernel β w.1 from (Real.exp_pos _).le)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfg _) hk) (hfg _)
    (hf _) (mul_nonneg hk (hgn _))

theorem finite_sum_gain_le {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (s : Finset I) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hcn : ∀ i ∈ s, ∀ p, 0 ≤ c i p) (hcR : ∀ i ∈ s, ∀ p, c i p ≤ R)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    ∑ i ∈ s, gain β b (c i) (c i) p ≤ gain β b F F p := by
  have hci (i) (hi : i ∈ s) : Integrable (integrand β b (c i) (c i) p) (volume.prod sphereArea) := by
    have ha (q) : |c i q| ≤ R := by rw [abs_of_nonneg (hcn i hi q)]; exact hcR i hi q
    exact integrable_gain hβ hb hR hR (hcm i hi) (hcm i hi) ha ha p
  have hFa (q) : |F q| ≤ R := by rw [abs_of_nonneg (hF q).1]; exact (hF q).2
  change ∑ i ∈ s, (∫ w, integrand β b (c i) (c i) p w ∂(volume.prod sphereArea)) ≤ _
  rw [← integral_finsetSum _ hci]
  apply integral_mono (integrable_finsetSum s hci)
    (integrable_gain hβ hb hR hR hFm hFm hFa hFa p)
  intro w
  have hdiag : (∑ i ∈ s, c i (p.1, scatterLeft p.2 w.1 w.2) * c i (p.1, scatterRight p.2 w.1 w.2)) ≤
      F (p.1, scatterLeft p.2 w.1 w.2) * F (p.1, scatterRight p.2 w.1 w.2) := by
    calc
      _ ≤ ∑ i ∈ s, c i (p.1, scatterLeft p.2 w.1 w.2) *
          (∑ j ∈ s, c j (p.1, scatterRight p.2 w.1 w.2)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j hj => hcn j hj _) hi) (hcn i hi _)
      _ = (∑ i ∈ s, c i (p.1, scatterLeft p.2 w.1 w.2)) *
          (∑ i ∈ s, c i (p.1, scatterRight p.2 w.1 w.2)) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul (hSum _) (hSum _) (Finset.sum_nonneg (fun i hi => hcn i hi _)) (hF _).1
  unfold integrand
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiag
    (Real.exp_pos _).le) (CollisionCutoff.kernel_nonneg _ _ _ _)

theorem gain_tendsto {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfR : ∀ n p, |f n p| ≤ R)
    (hlim : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p))) (p : X × Velocity) :
    Tendsto (fun n => gain β b (f n) (f n) p) atTop (𝓝 (gain β b g g p)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun w : Velocity × Sphere => (b * R * R) * JetGaussianMoments.kernel β w.1)
  · intro n
    exact (integrable_gain hβ hb hR hR (hfm n) (hfm n) (hfR n) (hfR n) p).aestronglyMeasurable
  · exact majorant_integrable hβ _
  · intro n
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using integrand_bound hb hR hR (hfR n) (hfR n) β p w)
  · exact ae_of_all _ (fun w => (tendsto_const_nhds.mul (hlim (p.1, scatterLeft p.2 w.1 w.2))).mul
      (hlim (p.1, scatterRight p.2 w.1 w.2)))

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-!
# Centered Gaussians as mixtures of uniform disks

The mixing density in Section 3 is `2 a³ / d⁴ * exp (-a²/d²)` on positive
radii. The formulas below retain the ordinary, unnormalized Lebesgue density
of each disk so that the normalization factors remain explicit.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.GaussianDiskMixture

def gaussianDensity (d : ℝ) (p : Transverse) : ℝ :=
  (Real.pi * d ^ 2)⁻¹ * Real.exp (-‖p‖ ^ 2 / d ^ 2)

def diskDensity (a : ℝ) (p : Transverse) : ℝ :=
  (ball (0 : Transverse) a).indicator (fun _ => (Real.pi * a ^ 2)⁻¹) p

def mixingDensity (d a : ℝ) : ℝ :=
  2 * a ^ 3 / d ^ 4 * Real.exp (-a ^ 2 / d ^ 2)

theorem gaussianDensity_nonneg (d : ℝ) (p : Transverse) : 0 ≤ gaussianDensity d p := by
  unfold gaussianDensity
  positivity

theorem diskDensity_nonneg (a : ℝ) (p : Transverse) : 0 ≤ diskDensity a p := by
  unfold diskDensity
  apply indicator_nonneg _ p
  intro x hx
  positivity

theorem mixingDensity_nonneg (d : ℝ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ mixingDensity d a := by
  unfold mixingDensity
  positivity

theorem measurable_gaussianDensity (d : ℝ) : Measurable (gaussianDensity d) := by
  unfold gaussianDensity
  fun_prop

theorem measurable_mixingDensity (d : ℝ) : Measurable (mixingDensity d) := by
  unfold mixingDensity
  fun_prop

theorem diskDensity_eq_ite (a : ℝ) (p : Transverse) :
    diskDensity a p = if ‖p‖ < a then (Real.pi * a ^ 2)⁻¹ else 0 := by
  simp [diskDensity, indicator]

theorem measurable_diskDensity : Measurable (fun ap : ℝ × Transverse => diskDensity ap.1 ap.2) := by
  simp only [diskDensity_eq_ite]
  apply Measurable.ite (measurableSet_lt measurable_snd.norm measurable_fst) <;> fun_prop

theorem integrableOn_mixingDensity {d : ℝ} (hd : 0 < d) :
    IntegrableOn (mixingDensity d) (Ioi 0) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / d ^ 2)
    (by positivity) (show (-1 : ℝ) < 3 by norm_num)).const_mul (2 / d ^ 4)
  change Integrable _ _
  convert hi using 1
  funext a
  simp only [mixingDensity, Real.rpow_ofNat]
  rw [show -(1 / d ^ 2) * a ^ 2 = -a ^ 2 / d ^ 2 by ring]
  ring

private theorem integral_gaussian_tail {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (∫ a in Ioi r, a * Real.exp (-b * a ^ 2)) =
      (2 * b)⁻¹ * Real.exp (-b * r ^ 2) := by
  have hb₀ : b ≠ 0 := hb.ne'
  have hderiv : ∀ a : ℝ, HasDerivAt
      (fun a => -(2 * b)⁻¹ * Real.exp (-b * a ^ 2))
      (a * Real.exp (-b * a ^ 2)) a := by
    intro a
    convert (((hasDerivAt_pow 2 a).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)) using 1
    field_simp
    ring
  have hi : Integrable (fun a : ℝ => a * Real.exp (-b * a ^ 2)) := by
    simpa only [Real.rpow_one] using
      integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 1 by norm_num)
  have ht : Tendsto (fun a : ℝ => -(2 * b)⁻¹ * Real.exp (-b * a ^ 2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
    simpa only [mul_zero, Function.comp_def] using h.const_mul (-(2 * b)⁻¹)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := r) (fun a _ => hderiv a) hi.integrableOn ht
  simpa only [zero_sub, neg_mul, neg_neg] using h

theorem integral_radius_tail {d : ℝ} (hd : 0 < d) (r : ℝ) :
    (∫ a in Ioi r, a * Real.exp (-a ^ 2 / d ^ 2)) =
      d ^ 2 / 2 * Real.exp (-r ^ 2 / d ^ 2) := by
  have h := integral_gaussian_tail (b := 1 / d ^ 2) (by positivity) r
  convert h using 1
  · congr 1
    funext a
    congr 2
    ring
  · congr 1 <;> field_simp

private theorem integral_radius_cubic {d : ℝ} (hd : 0 < d) :
    (∫ a in Ioi (0 : ℝ), a ^ 3 * Real.exp (-a ^ 2 / d ^ 2)) = d ^ 4 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun a : ℝ => Real.exp (-(1 / d ^ 2) * a ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 4)) (b := 1 / d ^ 2) (by positivity)
  rw [hg] at h
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)] at h
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  norm_num [finrank_euclideanSpace, Real.rpow_natCast] at h
  have hd₀ : d ≠ 0 := hd.ne'
  have hrewrite : (fun a : ℝ => a ^ 3 * Real.exp (-((d ^ 2)⁻¹ * a ^ 2))) =
      fun a => a ^ 3 * Real.exp (-a ^ 2 / d ^ 2) := by funext a; congr 2; ring
  rw [hrewrite] at h
  field_simp at h
  simp only [neg_div] at ⊢
  linarith

theorem integral_mixingDensity {d : ℝ} (hd : 0 < d) :
    (∫ a in Ioi (0 : ℝ), mixingDensity d a) = 1 := by
  have heq : mixingDensity d = fun a => (2 / d ^ 4) *
      (a ^ 3 * Real.exp (-a ^ 2 / d ^ 2)) := by
    funext a
    unfold mixingDensity
    ring
  rw [heq, integral_const_mul, integral_radius_cubic hd]
  field_simp

private theorem layerCake_integrand {d : ℝ} (hd : 0 < d) (p : Transverse)
    {a : ℝ} (ha : 0 < a) :
    mixingDensity d a * diskDensity a p =
      (Ioi ‖p‖).indicator (fun a => (2 / (Real.pi * d ^ 4)) *
        (a * Real.exp (-a ^ 2 / d ^ 2))) a := by
  have hd₀ : d ≠ 0 := hd.ne'
  have ha₀ : a ≠ 0 := ha.ne'
  by_cases hp : ‖p‖ < a
  · simp only [mixingDensity, diskDensity, indicator_of_mem
      (show p ∈ ball (0 : Transverse) a from mem_ball_zero_iff.mpr hp),
      indicator_of_mem (show a ∈ Ioi ‖p‖ from hp)]
    field_simp
  · simp only [diskDensity, indicator_of_notMem
      (show p ∉ ball (0 : Transverse) a from fun h => hp (mem_ball_zero_iff.mp h)),
      mul_zero, indicator_of_notMem (show a ∉ Ioi ‖p‖ from hp)]

theorem integrableOn_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    IntegrableOn (fun a => mixingDensity d a * diskDensity a p) (Ioi 0) := by
  have hi : Integrable (fun a : ℝ => a * Real.exp (-a ^ 2 / d ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / d ^ 2)
      (by positivity) (show (-1 : ℝ) < 1 by norm_num)
    convert h using 1
    funext a
    rw [Real.rpow_one]
    congr 2
    ring
  have hc := (hi.const_mul (2 / (Real.pi * d ^ 4))).indicator
    (measurableSet_Ioi (a := ‖p‖))
  exact hc.integrableOn.congr_fun (fun a ha => (layerCake_integrand hd p ha).symm)
    measurableSet_Ioi

/-- Pointwise layer-cake identity, with the positive-radius mixing law normalized below. -/
theorem density_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    (∫ a in Ioi (0 : ℝ), mixingDensity d a * diskDensity a p) = gaussianDensity d p := by
  have hd₀ : d ≠ 0 := hd.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha => layerCake_integrand hd p ha),
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left (norm_nonneg p), integral_const_mul, integral_radius_tail hd]
  unfold gaussianDensity
  field_simp

theorem lintegral_density_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a * diskDensity a p)) =
      ENNReal.ofReal (gaussianDensity d p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_layerCake hd p), density_layerCake hd]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact mul_nonneg (mixingDensity_nonneg d (le_of_lt ha)) (diskDensity_nonneg a p)

theorem lintegral_mixingDensity {d : ℝ} (hd : 0 < d) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_mixingDensity hd),
    integral_mixingDensity hd, ENNReal.ofReal_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact mixingDensity_nonneg d (le_of_lt ha)

private theorem lintegral_diskDensity_mul (φ : Transverse → ℝ≥0∞) (a : ℝ) (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (diskDensity a p) * φ p) =
      (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p := by
  have heq : (fun p => ENNReal.ofReal (diskDensity a p) * φ p) =
      (ball (0 : Transverse) a).indicator
        (fun p => ENNReal.ofReal ((Real.pi * a ^ 2)⁻¹) * φ p) := by
    funext p
    by_cases hp : p ∈ ball (0 : Transverse) a <;> simp [diskDensity, indicator, hp]
  rw [heq, lintegral_indicator measurableSet_ball,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_inv_of_pos (by positivity)]

private theorem measurable_layerCake (d : ℝ) (φ : Transverse → ℝ≥0∞)
    (hφ : Measurable φ) : Measurable (fun pa : Transverse × ℝ =>
      ENNReal.ofReal (mixingDensity d pa.2 * diskDensity pa.2 pa.1) * φ pa.1) := by
  have hs : Measurable (Prod.swap : Transverse × ℝ → ℝ × Transverse) := measurable_swap
  have hdp := measurable_diskDensity.comp hs
  have hm := (measurable_mixingDensity d).comp
    (measurable_snd : Measurable (Prod.snd : Transverse × ℝ → ℝ))
  have hprod := hm.mul hdp
  have hr := hprod.ennreal_ofReal
  have hp := hφ.comp (measurable_fst : Measurable (Prod.fst : Transverse × ℝ → Transverse))
  have h := hr.mul hp
  simpa only [Function.comp_def, Pi.mul_def, Prod.fst_swap, Prod.snd_swap] using h

private theorem lintegral_layerCake_mul {d : ℝ} (hd : 0 < d)
    (φ : Transverse → ℝ≥0∞) (p : Transverse) :
    (∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p) =
      ENNReal.ofReal (gaussianDensity d p) * φ p := by
  have hm : Measurable (fun a => ENNReal.ofReal (mixingDensity d a * diskDensity a p)) :=
    ((measurable_mixingDensity d).mul
      (measurable_diskDensity.comp (measurable_id.prodMk measurable_const))).ennreal_ofReal
  rw [lintegral_mul_const _ hm, lintegral_density_layerCake hd]

private theorem lintegral_layerCake_disk {d a : ℝ} (φ : Transverse → ℝ≥0∞)
    (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p) =
      ENNReal.ofReal (mixingDensity d a) *
        ((ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p) := by
  simp_rw [ENNReal.ofReal_mul (mixingDensity_nonneg d ha.le), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_diskDensity_mul φ a ha]

/-- Tonelli's theorem expresses every nonnegative measurable Gaussian expectation
as a probability mixture of normalized disk expectations. -/
theorem lintegral_gaussian_mixture {d : ℝ} (hd : 0 < d)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p) * φ p) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) *
        ((ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p) := by
  calc
    _ = ∫⁻ p, ∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p :=
      lintegral_congr (fun p => (lintegral_layerCake_mul hd φ p).symm)
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p,
        ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p :=
      lintegral_lintegral_swap (measurable_layerCake d φ hφ).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact lintegral_layerCake_disk φ ha

theorem integrable_diskDensity {a : ℝ} (_ha : 0 < a) : Integrable (diskDensity a) := by
  apply (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball

theorem integral_diskDensity {a : ℝ} (ha : 0 < a) : (∫ p, diskDensity a p) = 1 := by
  unfold diskDensity
  rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul,
    TransverseDisk.disk_volume_real 0 ha.le]
  field_simp

theorem lintegral_diskDensity {a : ℝ} (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (diskDensity a p)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_diskDensity ha)
    (ae_of_all _ (diskDensity_nonneg a)), integral_diskDensity ha, ENNReal.ofReal_one]

theorem lintegral_gaussianDensity {d : ℝ} (hd : 0 < d) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p)) = 1 := by
  have h := lintegral_gaussian_mixture hd (fun _ => 1) measurable_const
  simp only [mul_one] at h
  rw [h]
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have hn := lintegral_diskDensity_mul (fun _ => 1) a ha
      simp only [mul_one] at hn
      rw [← hn, lintegral_diskDensity ha, mul_one]
    _ = 1 := lintegral_mixingDensity hd

def gaussianLaw (d : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (gaussianDensity d p))

def uniformDiskLaw (a : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (diskDensity a p))

def mixingRadiusLaw (d : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun a => ENNReal.ofReal (mixingDensity d a))

theorem gaussianLaw_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (gaussianLaw d) := by
  constructor
  rw [gaussianLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_gaussianDensity hd]

theorem uniformDiskLaw_isProbabilityMeasure {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (uniformDiskLaw a) := by
  constructor
  rw [uniformDiskLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_diskDensity ha]

theorem mixingRadiusLaw_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (mixingRadiusLaw d) := by
  constructor
  rw [mixingRadiusLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_mixingDensity hd]

theorem uniformDiskLaw_lintegral {a : ℝ} (ha : 0 < a)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, φ p ∂uniformDiskLaw a) =
      (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p := by
  have hmk : Measurable (fun p : Transverse => (a, p)) :=
    measurable_const.prodMk measurable_id
  have hda : Measurable (diskDensity a) := by
    simpa only [Function.comp_def] using measurable_diskDensity.comp hmk
  rw [uniformDiskLaw, lintegral_withDensity_eq_lintegral_mul volume hda.ennreal_ofReal hφ]
  exact lintegral_diskDensity_mul φ a ha

/-- The centered Gaussian law is the probability mixture of normalized disk laws
with radius density `mixingDensity d` on the positive half-line. -/
theorem gaussianLaw_mixture {d : ℝ} (hd : 0 < d)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, φ p ∂gaussianLaw d) =
      ∫⁻ a, (∫⁻ p, φ p ∂uniformDiskLaw a) ∂mixingRadiusLaw d := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal (gaussianDensity d p) * φ p := by
      rw [gaussianLaw, lintegral_withDensity_eq_lintegral_mul volume
        (measurable_gaussianDensity d).ennreal_ofReal hφ]
      rfl
    _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) *
        ((ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p) :=
      lintegral_gaussian_mixture hd φ hφ
    _ = _ := by
      rw [mixingRadiusLaw, lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (measurable_mixingDensity d).ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      change _ = ENNReal.ofReal (mixingDensity d a) * (∫⁻ p, φ p ∂uniformDiskLaw a)
      rw [uniformDiskLaw_lintegral ha φ hφ]

theorem gaussian_kernel_lintegral_le {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p) *
      ENNReal.ofReal (kernel q (direction v) (v - p))) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hm : Measurable (fun p => kernel q (direction v) (v - p)) := by
    unfold kernel
    fun_prop
  rw [lintegral_gaussian_mixture hd _ hm.ennreal_ofReal]
  calc
    _ ≤ ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) *
        ENNReal.ofReal (expectationConstant q / ‖v‖) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have ha₀ : 0 < a := ha
      apply mul_le_mul_right
      have hi := integrableOn_kernel_translatedDisk hq₂ ha₀ (direction v) (norm_direction hv) v
      have heq : (∫⁻ p in ball (0 : Transverse) a,
          ENNReal.ofReal (kernel q (direction v) (v - p))) =
          ENNReal.ofReal (∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hi
          (ae_of_all _ (fun p => kernel_nonneg q (direction v) (v - p)))
      rw [heq]
      have hnorm : (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ *
          ENNReal.ofReal (∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) =
          ENNReal.ofReal ((∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) /
            (Real.pi * a ^ 2)) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv, mul_comm]
      rw [hnorm]
      exact ENNReal.ofReal_le_ofReal (uniformDisk_expectation_le hq₁ hq₂ ha₀ hv)
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_mixingDensity hd, one_mul]

theorem integrable_gaussian_kernel {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    Integrable (fun p => gaussianDensity d p * kernel q (direction v) (v - p)) := by
  have hm : Measurable (fun p => gaussianDensity d p * kernel q (direction v) (v - p)) := by
    unfold gaussianDensity kernel
    fun_prop
  have hn : 0 ≤ᵐ[volume] (fun p => gaussianDensity d p * kernel q (direction v) (v - p)) :=
    ae_of_all _ (fun p => mul_nonneg (gaussianDensity_nonneg d p)
      (kernel_nonneg q (direction v) (v - p)))
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp
  have hb := gaussian_kernel_lintegral_le hq₁ hq₂ hd hv
  simp_rw [← ENNReal.ofReal_mul (gaussianDensity_nonneg d _)] at hb
  exact ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)

theorem gaussian_kernel_expectation_le {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    (∫ p, gaussianDensity d p * kernel q (direction v) (v - p)) ≤
      expectationConstant q / ‖v‖ := by
  have hi := integrable_gaussian_kernel hq₁ hq₂ hd hv
  have hn : 0 ≤ᵐ[volume] (fun p => gaussianDensity d p * kernel q (direction v) (v - p)) :=
    ae_of_all _ (fun p => mul_nonneg (gaussianDensity_nonneg d p)
      (kernel_nonneg q (direction v) (v - p)))
  apply (ENNReal.ofReal_le_ofReal_iff (by
    exact div_nonneg (expectationConstant_pos q).le (norm_nonneg v))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  simp_rw [ENNReal.ofReal_mul (gaussianDensity_nonneg d _)]
  exact gaussian_kernel_lintegral_le hq₁ hq₂ hd hv

theorem gaussianLaw_kernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (kernel q (direction v) (v - p)) ∂gaussianLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hm : Measurable (fun p => ENNReal.ofReal (kernel q (direction v) (v - p))) := by
    unfold kernel
    fun_prop
  rw [gaussianLaw, lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gaussianDensity d).ennreal_ofReal hm]
  exact gaussian_kernel_lintegral_le hq₁ hq₂ hd hv

end BoltzmannNonuniqueness.GaussianDiskMixture

end

end

section

/-!
# Gaussian parameter laws for compressed sheets

The probability and exponential-moment assertions in `ker:parameter-sheets`
use only measurable axial maps. Both the original axial Gaussian (variance
`1 / 2`) and the widened Gaussian (variance `1`) satisfy the bounds below.
The collision gain estimate is not assumed or asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness.GaussianSheets

/-- The axial image law, with variance parameter as in Mathlib's Gaussian. -/
def axialLaw (v : ℝ≥0) (Φ : ℝ → ℝ) : Measure ℝ :=
  (gaussianReal 0 v).map Φ

instance axialLaw_isProbabilityMeasure (v : ℝ≥0) (Φ : ℝ → ℝ) :
    IsProbabilityMeasure (axialLaw v Φ) := by
  unfold axialLaw
  infer_instance

theorem axialLaw_univ (v : ℝ≥0) (Φ : ℝ → ℝ) : axialLaw v Φ univ = 1 :=
  measure_univ

theorem original_gaussian_density (a : ℝ) :
    gaussianPDFReal 0 (1 / 2) a = (Real.sqrt Real.pi)⁻¹ * Real.exp (-a ^ 2) := by
  unfold gaussianPDFReal
  norm_num
  have h₂ : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp

theorem wider_gaussian_density (a : ℝ) :
    gaussianPDFReal 0 1 a = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-a ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]

private theorem integrable_gaussianReal_iff {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 v) ↔
      Integrable (fun a => gaussianPDFReal 0 v a * f a) := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    smul_eq_mul]

/-- A quadratic exponential changes the centered Gaussian variance by a factor of two. -/
theorem gaussianPDF_mul_exp_quarter {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    gaussianPDFReal 0 v a * Real.exp (a ^ 2 / (4 * (v : ℝ))) =
      Real.sqrt 2 * gaussianPDFReal 0 (2 * v) a := by
  have hv₀ : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hs : Real.sqrt (2 * Real.pi * (2 * (v : ℝ))) =
      Real.sqrt 2 * Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [show 2 * Real.pi * (2 * (v : ℝ)) = 2 * (2 * Real.pi * (v : ℝ)) by ring,
      Real.sqrt_mul (by norm_num)]
  have he : -a ^ 2 / (2 * (v : ℝ)) + a ^ 2 / (4 * (v : ℝ)) =
      -a ^ 2 / (2 * (2 * (v : ℝ))) := by field_simp; ring
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [mul_assoc, ← Real.exp_add, he, hs]
  have hs₀ : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 := by positivity
  have h₂ : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp

theorem integrable_exp_quarter_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun a : ℝ => Real.exp (a ^ 2 / (4 * (v : ℝ)))) (gaussianReal 0 v) := by
  apply (integrable_gaussianReal_iff hv _).mpr
  have hi := (integrable_gaussianPDFReal 0 (2 * v)).const_mul (Real.sqrt 2)
  exact hi.congr (ae_of_all _ (fun a => (gaussianPDF_mul_exp_quarter hv a).symm))

theorem integral_exp_quarter_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ a : ℝ, Real.exp (a ^ 2 / (4 * (v : ℝ))) ∂gaussianReal 0 v) = Real.sqrt 2 := by
  have h₂v : (2 : ℝ≥0) * v ≠ 0 := mul_ne_zero (by norm_num) hv
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, gaussianPDF_mul_exp_quarter hv, integral_const_mul,
    integral_gaussianPDFReal_eq_one 0 h₂v, mul_one]

private theorem exp_image_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) (a : ℝ) :
    Real.exp (8 * (Φ a) ^ 2) ≤
      Real.exp (16 * A ^ 2) * Real.exp (a ^ 2 / (4 * (v : ℝ))) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hvle : (v : ℝ) ≤ 1 := by exact_mod_cast hv₁
  have hsq : (Φ a) ^ 2 ≤ (A + δ * |a|) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Φ a)) (by positivity)).mpr (hΦ a)
  have hδsq : 16 * δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
  have hsplit : 8 * (Φ a) ^ 2 ≤ 16 * A ^ 2 + a ^ 2 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hδsq (sq_nonneg a)
    nlinarith [sq_nonneg (A - δ * |a|), sq_abs a]
  have hdiv : a ^ 2 / 4 ≤ a ^ 2 / (4 * (v : ℝ)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
    linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The Gaussian parameter integrand is genuinely integrable, before taking its image law. -/
theorem integrable_exp_image {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    Integrable (fun a => Real.exp (8 * (Φ a) ^ 2)) (gaussianReal 0 v) := by
  apply ((integrable_exp_quarter_gaussian hv).const_mul (Real.exp (16 * A ^ 2))).mono'
  · exact (by fun_prop : Measurable (fun a => Real.exp (8 * (Φ a) ^ 2))).aestronglyMeasurable
  · filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_image_le hv hv₁ hA hδ hδ₁ hΦ a

/-- The constant `2 * exp (16 * A²)` works for the original and wider parameter laws. -/
theorem integral_exp_image_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    (∫ a, Real.exp (8 * (Φ a) ^ 2) ∂gaussianReal 0 v) ≤ 2 * Real.exp (16 * A ^ 2) := by
  calc
    _ ≤ ∫ a, Real.exp (16 * A ^ 2) * Real.exp (a ^ 2 / (4 * (v : ℝ)))
        ∂gaussianReal 0 v :=
      integral_mono (integrable_exp_image hv hv₁ hA hδ hδ₁ hΦm hΦ)
        ((integrable_exp_quarter_gaussian hv).const_mul _) (exp_image_le hv hv₁ hA hδ hδ₁ hΦ)
    _ = Real.exp (16 * A ^ 2) * Real.sqrt 2 := by
      rw [integral_const_mul, integral_exp_quarter_gaussian hv]
    _ ≤ _ := by
      have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
        apply Real.sqrt_le_iff.mpr
        norm_num
      nlinarith [Real.exp_pos (16 * A ^ 2)]

theorem integrable_axialLaw_exp {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) (axialLaw v Φ) := by
  apply (integrable_map_measure (by fun_prop) hΦm.aemeasurable).mpr
  exact integrable_exp_image hv hv₁ hA hδ hδ₁ hΦm hΦ

theorem integral_axialLaw_exp_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    (∫ a : ℝ, Real.exp (8 * a ^ 2) ∂axialLaw v Φ) ≤ 2 * Real.exp (16 * A ^ 2) := by
  rw [axialLaw, integral_map hΦm.aemeasurable (by fun_prop)]
  exact integral_exp_image_le hv hv₁ hA hδ hδ₁ hΦm hΦ

/-- The parameter-tail estimate widens the Gaussian and extracts its uniform decay factor. -/
theorem gaussian_parameter_tail {B : ℝ} (hB : 0 ≤ B) (w : Velocity) :
    {u : Velocity | B < ‖u‖}.indicator (fun u => Real.exp (-‖u‖ ^ 2)) w ≤
      Real.exp (-B ^ 2 / 2) * Real.exp (-‖w‖ ^ 2 / 2) := by
  by_cases hw : B < ‖w‖
  · rw [indicator_of_mem (show w ∈ {u : Velocity | B < ‖u‖} from hw), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : B ^ 2 ≤ ‖w‖ ^ 2 := (sq_le_sq₀ hB (norm_nonneg w)).mpr hw.le
    linarith
  · rw [indicator_of_notMem (show w ∉ {u : Velocity | B < ‖u‖} from hw)]
    positivity

end BoltzmannNonuniqueness.GaussianSheets

end

end

section

/-! # The positive source used for the fixed-cutoff iteration -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X : Type*} [MeasurableSpace X]

def source (β b L : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain β b f f p + (L - frequency β b f p) * f p

theorem measurable_source {f : X × Velocity → ℝ} (hf : Measurable f) (β b L : ℝ) :
    Measurable (source β b L f) :=
  (measurable_gain hf hf β b).add ((measurable_const.sub (measurable_frequency hf β b)).mul hf)

omit [MeasurableSpace X] in
theorem source_bounds {β b L R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : lossConstant β b * R ≤ L) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (p : X × Velocity) :
    0 ≤ source β b L f p ∧ source β b L f p ≤ gainConstant β b * R ^ 2 + L * R := by
  have hfabs (q) : |f q| ≤ R := by rw [abs_of_nonneg (hf q).1]; exact (hf q).2
  have hν := frequency_nonneg (fun q => (hf q).1) β b p
  have hνbound : frequency β b f p ≤ lossConstant β b * R :=
    (le_abs_self _).trans (frequency_bound hβ hb hfabs p)
  have hLpos : 0 ≤ L := (mul_nonneg (constants_nonneg hb β).2 hR).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun q => (hf q).1) (fun q => (hf q).1) β b p)
      (mul_nonneg (sub_nonneg.mpr (hνbound.trans hL)) (hf p).1)
  · have hg := (le_abs_self _).trans (gain_bound hβ hb hR hR hfabs hfabs p)
    have hl : (L - frequency β b f p) * f p ≤ L * R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hf p).1).trans
        (mul_le_mul_of_nonneg_left (hf p).2 hLpos)
    change gain β b f f p + (L - frequency β b f p) * f p ≤ _
    nlinarith only [hg, hl]

theorem source_difference {β b L R D : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ R)
    (hfg : ∀ p, |f p - g p| ≤ D) (p : X × Velocity) :
    |source β b L f p - source β b L g p| ≤
      (2 * R * (gainConstant β b + lossConstant β b) + L) * D := by
  have hfabs (q) : |f q| ≤ R := by rw [abs_of_nonneg (hf q).1]; exact (hf q).2
  have hgabs (q) : |g q| ≤ R := by rw [abs_of_nonneg (hg q).1]; exact (hg q).2
  have hgain := gain_difference hβ hb hR hR hD hfm hgm hfabs hgabs hfg p
  have hνdiff := frequency_difference hβ hb hfm hgm hfabs hgabs hfg p
  have hνfb := frequency_bound hβ hb hfabs p
  have hloss : |frequency β b f p * f p - frequency β b g p * g p| ≤
      2 * lossConstant β b * R * D := by
    calc
      _ = |frequency β b f p * (f p - g p) +
          (frequency β b f p - frequency β b g p) * g p| := by congr 1; ring
      _ ≤ |frequency β b f p| * |f p - g p| +
          |frequency β b f p - frequency β b g p| * |g p| := by
        simpa only [abs_mul] using abs_add_le (frequency β b f p * (f p - g p))
          ((frequency β b f p - frequency β b g p) * g p)
      _ ≤ (lossConstant β b * R) * D + (lossConstant β b * D) * R :=
        add_le_add (mul_le_mul hνfb (hfg p) (abs_nonneg _) (mul_nonneg (constants_nonneg hb β).2 hR))
          (mul_le_mul hνdiff (hgabs p) (abs_nonneg _) (mul_nonneg (constants_nonneg hb β).2 hD))
      _ = _ := by ring
  calc
    _ = |(gain β b f f p - gain β b g g p) + L * (f p - g p) -
        (frequency β b f p * f p - frequency β b g p * g p)| := by unfold source; congr 1; ring
    _ ≤ |gain β b f f p - gain β b g g p| + L * |f p - g p| +
        |frequency β b f p * f p - frequency β b g p * g p| := by
      have ha : |(gain β b f f p - gain β b g g p) + L * (f p - g p)| ≤
          |gain β b f f p - gain β b g g p| + L * |f p - g p| := by
        simpa only [abs_mul, abs_of_nonneg hL] using
          (abs_add_le (gain β b f f p - gain β b g g p) (L * (f p - g p)))
      exact (abs_sub _ _).trans (add_le_add ha le_rfl)
    _ ≤ gainConstant β b * D * (R + R) + L * D + 2 * lossConstant β b * R * D :=
      add_le_add (add_le_add hgain (mul_le_mul_of_nonneg_left (hfg p) hL)) hloss
    _ = _ := by ring

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-! # Cold-color source with a common total loss frequency -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X : Type*} [MeasurableSpace X]

def coldSource (β b L : ℝ) (F c : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain β b c c p + (L - frequency β b F p) * c p

theorem measurable_coldSource {F c : X × Velocity → ℝ} (hF : Measurable F) (hc : Measurable c)
    (β b L : ℝ) : Measurable (coldSource β b L F c) :=
  (measurable_gain hc hc β b).add ((measurable_const.sub (measurable_frequency hF β b)).mul hc)

omit [MeasurableSpace X] in
theorem coldSource_bounds {β b L R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : lossConstant β b * R ≤ L) {F c : X × Velocity → ℝ}
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (p : X × Velocity) :
    0 ≤ coldSource β b L F c p ∧ coldSource β b L F c p ≤ gainConstant β b * R ^ 2 + L * R := by
  have hFa (q) : |F q| ≤ R := by rw [abs_of_nonneg (hF q).1]; exact (hF q).2
  have hca (q) : |c q| ≤ R := by rw [abs_of_nonneg (hc q).1]; exact (hc q).2
  have hν := frequency_nonneg (fun q => (hF q).1) β b p
  have hνbound : frequency β b F p ≤ lossConstant β b * R :=
    (le_abs_self _).trans (frequency_bound hβ hb hFa p)
  have hLpos := (mul_nonneg (constants_nonneg hb β).2 hR).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun q => (hc q).1) (fun q => (hc q).1) β b p)
      (mul_nonneg (sub_nonneg.mpr (hνbound.trans hL)) (hc p).1)
  · have hg := (le_abs_self _).trans (gain_bound hβ hb hR hR hca hca p)
    have hl : (L - frequency β b F p) * c p ≤ L * R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hc p).1).trans
        (mul_le_mul_of_nonneg_left (hc p).2 hLpos)
    change gain β b c c p + (L - frequency β b F p) * c p ≤ _
    nlinarith only [hg, hl]

theorem coldSource_mono {β b L R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : lossConstant β b * R ≤ L) {F c d : X × Velocity → ℝ}
    (hcm : Measurable c) (hdm : Measurable d)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hcn : ∀ p, 0 ≤ c p) (hcd : ∀ p, c p ≤ d p) (hdR : ∀ p, d p ≤ R)
    (p : X × Velocity) : coldSource β b L F c p ≤ coldSource β b L F d p := by
  have hFa (q) : |F q| ≤ R := by rw [abs_of_nonneg (hF q).1]; exact (hF q).2
  have hν : frequency β b F p ≤ L :=
    ((le_abs_self _).trans (frequency_bound hβ hb hFa p)).trans hL
  exact add_le_add (gain_mono hβ hb hR hcm hdm hcn hcd hdR p)
    (mul_le_mul_of_nonneg_left (hcd p) (sub_nonneg.mpr hν))

theorem coldSource_tendsto {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (L : ℝ) (F : X × Velocity → ℝ)
    {c : ℕ → X × Velocity → ℝ} {d : X × Velocity → ℝ}
    (hcm : ∀ n, Measurable (c n)) (hcR : ∀ n p, |c n p| ≤ R)
    (hlim : ∀ p, Tendsto (fun n => c n p) atTop (𝓝 (d p))) (p : X × Velocity) :
    Tendsto (fun n => coldSource β b L F (c n) p) atTop (𝓝 (coldSource β b L F d p)) :=
  (gain_tendsto hβ hb hR hcm hcR hlim p).add (tendsto_const_nhds.mul (hlim p))

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-! # Finite families of cold colors stay below the total source -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_coldSource_le {β b L R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : lossConstant β b * R ≤ L) (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    ∑ i ∈ s, coldSource β b L F (c i) p ≤ source β b L F p := by
  have hFa (q) : |F q| ≤ R := by rw [abs_of_nonneg (hF q).1]; exact (hF q).2
  have hν : frequency β b F p ≤ L :=
    ((le_abs_self _).trans (frequency_bound hβ hb hFa p)).trans hL
  unfold coldSource source
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add
    (finite_sum_gain_le hβ hb hR s hcm hFm
      (fun i hi p => (hc i hi p).1) (fun i hi p => (hc i hi p).2) hF hSum p)
    (mul_le_mul_of_nonneg_left (hSum p) (sub_nonneg.mpr hν))

end BoltzmannNonuniqueness.GaussianCutoff

end

end

end OAI
