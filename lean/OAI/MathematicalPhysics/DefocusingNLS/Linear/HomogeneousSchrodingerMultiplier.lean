import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeOperator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap

namespace OAI

/-! # The ordinary Schrödinger multiplier in the faithful homogeneous space -/

open MeasureTheory
open scoped SchwartzMap ENNReal ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousSchrodingerPhase (t : ℝ) (ξ : E) : ℂ :=
  Complex.exp ((-t * ‖ξ‖ ^ 2 : ℝ) * Complex.I)

@[simp] theorem homogeneousSchrodingerPhase_norm (t : ℝ) (ξ : E) :
    ‖homogeneousSchrodingerPhase t ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem homogeneousSchrodingerPhase_continuous (t : ℝ) :
    Continuous (homogeneousSchrodingerPhase t) := by
  unfold homogeneousSchrodingerPhase
  fun_prop

theorem homogeneousSchrodingerPhase_temperate (t : ℝ) :
    (homogeneousSchrodingerPhase t).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_exp_mul_I.comp
    ((Function.HasTemperateGrowth.const (-t)).mul (Function.hasTemperateGrowth_norm_sq E))

theorem memLp_homogeneousSchrodingerPhase_mul (a k t : ℝ) (f : HomogeneousY a k) :
    MemLp (fun ξ => homogeneousSchrodingerPhase t ξ * f ξ) 2 (homogeneousFourierMeasure a k) := by
  apply (Lp.memLp f).of_le_mul (c := 1)
    ((homogeneousSchrodingerPhase_continuous t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact ae_of_all _ (fun ξ => by
    change ‖homogeneousSchrodingerPhase t ξ * f ξ‖ ≤ 1 * ‖f ξ‖
    simp only [norm_mul, homogeneousSchrodingerPhase_norm, one_mul]
    exact le_rfl)

noncomputable def homogeneousSchrodingerVector (a k t : ℝ) (f : HomogeneousY a k) :
    HomogeneousY a k :=
  (memLp_homogeneousSchrodingerPhase_mul a k t f).toLp
    (fun ξ => homogeneousSchrodingerPhase t ξ * f ξ)

theorem homogeneousSchrodingerVector_ae (a k t : ℝ) (f : HomogeneousY a k) :
    homogeneousSchrodingerVector a k t f =ᵐ[homogeneousFourierMeasure a k]
      (fun ξ => homogeneousSchrodingerPhase t ξ * f ξ) :=
  (memLp_homogeneousSchrodingerPhase_mul a k t f).coeFn_toLp

theorem homogeneousSchrodingerVector_norm (a k t : ℝ) (f : HomogeneousY a k) :
    ‖homogeneousSchrodingerVector a k t f‖ = ‖f‖ := by
  rw [homogeneousSchrodingerVector, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    ((homogeneousSchrodingerPhase_continuous t).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)) (Lp.aestronglyMeasurable f)
  exact ae_of_all _ (fun ξ => by
    change ‖homogeneousSchrodingerPhase t ξ * f ξ‖ = ‖f ξ‖
    simp only [norm_mul, homogeneousSchrodingerPhase_norm, one_mul])

noncomputable def homogeneousSchrodingerLinearMap (a k t : ℝ) :
    HomogeneousY a k →ₗ[ℂ] HomogeneousY a k where
  toFun := homogeneousSchrodingerVector a k t
  map_add' f g := by
    apply Lp.ext
    filter_upwards [homogeneousSchrodingerVector_ae a k t (f + g),
      homogeneousSchrodingerVector_ae a k t f, homogeneousSchrodingerVector_ae a k t g,
      Lp.coeFn_add f g, Lp.coeFn_add (homogeneousSchrodingerVector a k t f)
        (homogeneousSchrodingerVector a k t g)] with ξ hfg hf hg hsum hout
    rw [hfg, hsum, hout]
    simp only [Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [homogeneousSchrodingerVector_ae a k t (c • f),
      homogeneousSchrodingerVector_ae a k t f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (homogeneousSchrodingerVector a k t f)] with ξ hcf hf hin hout
    change homogeneousSchrodingerVector a k t (c • f) ξ =
      (c • homogeneousSchrodingerVector a k t f : HomogeneousY a k) ξ
    rw [hcf, hin, hout]
    simp only [Pi.smul_apply, smul_eq_mul, hf]
    ring

noncomputable def homogeneousSchrodingerOperator (a k t : ℝ) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  (homogeneousSchrodingerLinearMap a k t).mkContinuous 1
    (fun f => by
      change ‖homogeneousSchrodingerVector a k t f‖ ≤ 1 * ‖f‖
      rw [homogeneousSchrodingerVector_norm, one_mul])

@[simp] theorem homogeneousSchrodingerOperator_norm (a k t : ℝ) (f : HomogeneousY a k) :
    ‖homogeneousSchrodingerOperator a k t f‖ = ‖f‖ := homogeneousSchrodingerVector_norm a k t f

theorem homogeneousSchrodingerOperator_Schwartz (a k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    homogeneousSchrodingerOperator a k t (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk
        (SchwartzMap.smulLeftCLM ℂ (homogeneousSchrodingerPhase t) ψ) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  apply Lp.ext
  filter_upwards [homogeneousSchrodingerVector_ae a k t
    (homogeneousFrequencyEmbedding a k ha ha1 hk ψ),
    SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k),
    SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ (homogeneousSchrodingerPhase t) ψ)
      2 (homogeneousFourierMeasure a k)] with ξ hf hψ hS
  change homogeneousSchrodingerVector a k t
    (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) ξ = _
  rw [hf]
  change homogeneousSchrodingerPhase t ξ * ψ.toLp 2 (homogeneousFourierMeasure a k) ξ =
    (SchwartzMap.smulLeftCLM ℂ (homogeneousSchrodingerPhase t) ψ).toLp
      2 (homogeneousFourierMeasure a k) ξ
  rw [hψ, hS]
  exact (SchwartzMap.smulLeftCLM_apply_apply (homogeneousSchrodingerPhase_temperate t) ψ ξ).symm

/-- The physical representative of the usual free Schrödinger evolution. -/
theorem homogeneousSchrodingerOperator_physical (a k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousSchrodingerOperator a k t f) y =
      inverseRadianFourier (fun ξ => homogeneousSchrodingerPhase t ξ * f ξ) y := by
  have he := (homogeneousSchrodingerVector_ae a k t f).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  exact congrFun (inverseRadianFourier_congr_ae he) y

end DefocusingNLS

end OAI
