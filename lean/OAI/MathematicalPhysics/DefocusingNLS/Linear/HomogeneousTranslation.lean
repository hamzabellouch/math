import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization

namespace OAI

/-! # Isometric physical translations in the faithful homogeneous space

Fourier modulation preserves the exact Y norm. The physical realization
turns it into translation; consequently all point-evaluation functionals
have the same operator norm.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousTranslationPhase (y ξ : E) : ℂ :=
  Complex.exp ((inner ℝ ξ y : ℝ) * Complex.I)

@[simp] theorem homogeneousTranslationPhase_norm (y ξ : E) :
    ‖homogeneousTranslationPhase y ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem homogeneousTranslationPhase_continuous (y : E) :
    Continuous (homogeneousTranslationPhase y) := by
  unfold homogeneousTranslationPhase
  fun_prop

theorem memLp_homogeneousTranslation (a k : ℝ) (y : E) (f : HomogeneousY a k) :
    MemLp (fun ξ => homogeneousTranslationPhase y ξ * f ξ) 2 (homogeneousFourierMeasure a k) := by
  apply (Lp.memLp f).of_le_mul (c := 1)
    ((homogeneousTranslationPhase_continuous y).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact ae_of_all _ (fun ξ => by
    change ‖homogeneousTranslationPhase y ξ * f ξ‖ ≤ 1 * ‖f ξ‖
    rw [norm_mul, homogeneousTranslationPhase_norm])

noncomputable def homogeneousTranslationVector (a k : ℝ) (y : E) (f : HomogeneousY a k) :
    HomogeneousY a k :=
  (memLp_homogeneousTranslation a k y f).toLp (fun ξ => homogeneousTranslationPhase y ξ * f ξ)

theorem homogeneousTranslationVector_ae (a k : ℝ) (y : E) (f : HomogeneousY a k) :
    homogeneousTranslationVector a k y f =ᵐ[homogeneousFourierMeasure a k]
      (fun ξ => homogeneousTranslationPhase y ξ * f ξ) :=
  (memLp_homogeneousTranslation a k y f).coeFn_toLp

@[simp] theorem homogeneousTranslationVector_norm (a k : ℝ) (y : E) (f : HomogeneousY a k) :
    ‖homogeneousTranslationVector a k y f‖ = ‖f‖ := by
  rw [homogeneousTranslationVector, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    ((homogeneousTranslationPhase_continuous y).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable f)
  exact ae_of_all _ (fun ξ => by
    change ‖homogeneousTranslationPhase y ξ * f ξ‖ = ‖f ξ‖
    rw [norm_mul, homogeneousTranslationPhase_norm, one_mul])

theorem inverseRadianFourier_translation (f : E → ℂ) (x y : E) :
    inverseRadianFourier (fun ξ => homogeneousTranslationPhase y ξ * f ξ) x =
      inverseRadianFourier f (x + y) := by
  unfold inverseRadianFourier radianFourierIntegral
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun ξ => by
    simp only [homogeneousTranslationPhase, inner_neg_right, neg_neg, inner_add_right,
      Complex.ofReal_add, add_mul, Complex.exp_add]
    ring)

theorem homogeneousTranslationVector_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (x y : E) (f : HomogeneousY a k) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousTranslationVector a k y f) x =
      homogeneousPhysicalCLM a k ha ha1 hk f (x + y) := by
  have he := (homogeneousTranslationVector_ae a k y f).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  change inverseRadianFourier (homogeneousTranslationVector a k y f) x = inverseRadianFourier f (x + y)
  rw [inverseRadianFourier_congr_ae he, inverseRadianFourier_translation]

theorem homogeneousPointEvaluation_norm_const (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (y : E) :
    ‖homogeneousPointEvaluation a k ha ha1 hk y‖ =
      ‖homogeneousPointEvaluation a k ha ha1 hk 0‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have he := homogeneousTranslationVector_physical a k ha ha1 hk 0 y f
    simp only [zero_add] at he
    change ‖homogeneousPhysicalCLM a k ha ha1 hk f y‖ ≤ _
    rw [← he]
    exact ((homogeneousPointEvaluation a k ha ha1 hk 0).le_opNorm
      (homogeneousTranslationVector a k y f)).trans_eq (by rw [homogeneousTranslationVector_norm])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have he := homogeneousTranslationVector_physical a k ha ha1 hk y (-y) f
    simp only [add_neg_cancel] at he
    change ‖homogeneousPhysicalCLM a k ha ha1 hk f 0‖ ≤ _
    rw [← he]
    exact ((homogeneousPointEvaluation a k ha ha1 hk y).le_opNorm
      (homogeneousTranslationVector a k (-y) f)).trans_eq (by rw [homogeneousTranslationVector_norm])

end DefocusingNLS

end OAI
