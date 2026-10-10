import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain

namespace OAI

/-! # Real symmetric mixed gain and its nonnegative bounds -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.MixedRealGain

def integrand (f g : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) : ℝ :=
  collisionKernel v p.1 p.2 / 2 *
    (f (scatterLeft v p.1 p.2) * g (scatterRight v p.1 p.2) +
      g (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2))

def gain (f g : Velocity → ℝ) (v : Velocity) : ℝ :=
  ∫ p, integrand f g v p ∂gainPairMeasure

theorem integrand_nonneg {f g : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (v : Velocity) (p : Velocity × Sphere) :
    0 ≤ integrand f g v p :=
  mul_nonneg (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))
    (add_nonneg (mul_nonneg (hf _) (hg _)) (mul_nonneg (hg _) (hf _)))

theorem integrand_measurable {f g : Velocity → ℝ} (hf : Measurable f) (hg : Measurable g)
    (v : Velocity) : Measurable (integrand f g v) := by
  have hl : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.div_const 2).mul (((hf.comp hl).mul (hg.comp hr)).add ((hg.comp hl).mul (hf.comp hr)))

theorem integrand_symm (f g : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) :
    integrand f g v p = integrand g f v p := by unfold integrand; ring

theorem gain_symm (f g : Velocity → ℝ) (v : Velocity) : gain f g v = gain g f v := by
  unfold gain
  congr 1
  funext p
  exact integrand_symm f g v p

theorem gain_eq_symmetricGain (f g : Velocity → ℝ) (x : Position) (v : Velocity) :
    gain f g v = symmetricGain (fun p => f p.2) (fun p => g p.2) x v := rfl

theorem gain_self (f : Velocity → ℝ) (v : Velocity) :
    gain f f v = BoltzmannNonuniqueness.gain (fun p => f p.2) 0 v := by
  rw [gain_eq_symmetricGain f f 0 v, symmetricGain_self]

theorem nonnegative_eq_lintegral {f g : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (v : Velocity) :
    nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v =
      ∫⁻ p, ENNReal.ofReal (integrand f g v p) ∂gainPairMeasure := by
  unfold nonnegativeGain
  apply lintegral_congr
  intro p
  have he : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 =
      ENNReal.ofReal (collisionKernel v p.1 p.2 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← ENNReal.ofReal_mul (hf _), ← ENNReal.ofReal_mul (hg _),
    ← ENNReal.ofReal_add (mul_nonneg (hf _) (hg _)) (mul_nonneg (hg _) (hf _)), he,
    ← ENNReal.ofReal_mul (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))]
  rfl

theorem integrable_of_bound {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) {B : ℝ} (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v ≤
      ENNReal.ofReal B) : Integrable (integrand f g v) gainPairMeasure := by
  refine ⟨(integrand_measurable hfm hgm v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (integrand_nonneg hf hg v)),
    ← nonnegative_eq_lintegral hf hg v]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem gain_le_of_bound {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) {B : ℝ} (hB : 0 ≤ B) (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v ≤
      ENNReal.ofReal B) : gain f g v ≤ B := by
  have hi := integrable_of_bound hfm hgm hf hg v hb
  have he : gain f g v =
      (nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v).toReal := by
    rw [nonnegative_eq_lintegral hf hg]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (integrand_nonneg hf hg v)) hi.aestronglyMeasurable
  rw [he]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem integrand_mono {f g F G : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity) (p : Velocity × Sphere) :
    integrand f g v p ≤ integrand F G v p := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))
  exact add_le_add (mul_le_mul (hfF _) (hgG _) (hg _) ((hf _).trans (hfF _)))
    (mul_le_mul (hgG _) (hfF _) (hf _) ((hg _).trans (hgG _)))

theorem integrable_of_le {f g F G : Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity)
    (hi : Integrable (integrand F G v) gainPairMeasure) :
    Integrable (integrand f g v) gainPairMeasure := by
  apply hi.mono' (integrand_measurable hfm hgm v).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hf hg v p)]
  exact integrand_mono hf hg hfF hgG v p

theorem gain_mono {f g F G : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity)
    (hi : Integrable (integrand F G v) gainPairMeasure) : gain f g v ≤ gain F G v :=
  integral_mono (integrable_of_le hfm hgm hf hg hfF hgG v hi) hi (integrand_mono hf hg hfF hgG v)

theorem gain_const_mul_right (f g : Velocity → ℝ) (v : Velocity) (c : ℝ) :
    gain f (fun w => c * g w) v = c * gain f g v := by
  unfold gain
  rw [← integral_const_mul]
  congr 1
  funext p
  unfold integrand
  ring

theorem integrable_const_mul_right {f g : Velocity → ℝ} {v : Velocity}
    (hi : Integrable (integrand f g v) gainPairMeasure) (c : ℝ) :
    Integrable (integrand f (fun w => c * g w) v) gainPairMeasure := by
  convert hi.const_mul c using 1
  funext p
  unfold integrand
  ring

end BoltzmannNonuniqueness.MixedRealGain

end

end OAI
