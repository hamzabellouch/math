import Mathlib

namespace OAI

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.EuclideanSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedDistribution (g : E →ᵇ F) : 𝓢'(E,F) :=
  ((g.memLp_top (μ := volume)).toLp g : Lp F ⊤ volume)

lemma boundedDistribution_apply (g : E →ᵇ F) (φ : 𝓢(E,ℂ)) :
    boundedDistribution g φ = ∫ x, φ x • g x := by
  rw [boundedDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [g.memLp_top.coeFn_toLp] with x hx
  rw [hx]

lemma integral_fourierInv_smul (φ : 𝓢(E,ℂ)) (v : Lp F 1 (volume : Measure E)) :
    (∫ x, (𝓕⁻ φ) x • v x) = ∫ x, φ x • (𝓕⁻ (v : E → F)) x := by
  have hflip : (-(innerₗ E)).flip = -(innerₗ E) := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ E))
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner.neg φ.integrable
    (memLp_one_iff_integrable.mp (Lp.memLp v))
  rw [hflip] at h
  rw [SchwartzMap.fourierInv_coe]
  exact h

lemma inverseFourier_boundedDistribution (v : Lp F 1 (volume : Measure E)) :
    𝓕⁻ (v : 𝓢'(E,F)) = boundedDistribution (Real.Lp.fourierTransformInv v) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    boundedDistribution_apply]
  simpa using integral_fourierInv_smul φ v

theorem exists_boundedContinuous_representative {s : ℝ} (hs : Module.finrank ℝ E < 2*s)
    {u : 𝓢'(E,F)} (hu : TemperedDistribution.MemSobolev s 2 u) :
    ∃ g : E →ᵇ F, u = boundedDistribution g := by
  obtain ⟨v,hv⟩ := hu.fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  rw [← inverseFourier_boundedDistribution, ← hv, fourierInv_fourier_eq]

theorem H3_representative {u : 𝓢'(EuclideanSpace ℝ (Fin 4), F)}
    (hu : TemperedDistribution.MemSobolev 3 2 u) :
    ∃ g : EuclideanSpace ℝ (Fin 4) →ᵇ F, u = boundedDistribution g := by
  apply exists_boundedContinuous_representative _ hu
  norm_num

def fourierMeasure (μ : Measure E) [IsFiniteMeasure μ] : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ => charFun μ ((-2 * Real.pi) • ξ))
    (continuous_charFun.comp (continuous_const.smul continuous_id))
    (μ.real Set.univ) (fun _ => norm_charFun_le _)

lemma fourierMeasure_apply (μ : Measure E) [IsFiniteMeasure μ] (ξ : E) :
    fourierMeasure μ ξ =
      VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) 1 ξ := by
  change charFun μ ((-2 * Real.pi) • ξ) = _
  rw [charFun_eq_fourierIntegral']
  congr 1
  rw [smul_smul]
  have hp : -(2 * Real.pi)⁻¹ * (-2 * Real.pi) = 1 := by
    field_simp
  rw [hp, one_smul]

lemma fourier_measure_distribution (μ : Measure E) [IsFiniteMeasure μ] :
    𝓕 μ.toTemperedDistribution = boundedDistribution (fourierMeasure μ) := by
  ext φ
  rw [TemperedDistribution.fourier_apply, Measure.toTemperedDistribution_apply μ,
    boundedDistribution_apply]
  have hflip : (innerₗ E).flip = innerₗ E := by ext x y; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
    (μ := volume) (ν := μ) Real.continuous_fourierChar continuous_inner φ.integrable
    (integrable_const (μ := μ) (1:ℂ))
  rw [hflip] at h
  change (∫ ξ, (𝓕 (φ : E → ℂ)) ξ • (1 : ℂ) ∂μ) =
    ∫ x, φ x • VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) 1 x at h
  simp only [smul_eq_mul, mul_one] at h
  simpa only [SchwartzMap.fourier_coe, fourierMeasure_apply, smul_eq_mul] using h

lemma memLp_besselWeight {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖^2)^(-s/2))) 2 volume := by
  have hreal : MemLp (fun x : E => (1 + ‖x‖^2)^(-s/2)) 2 volume := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
      (by norm_num)
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s/2)).1.continuous.aestronglyMeasurable]
    suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    congr
    ring
  exact hreal.ofReal

theorem finite_measure_memSobolev {s : ℝ} (hs : Module.finrank ℝ E < 2*s)
    (μ : Measure E) [IsFiniteMeasure μ] :
    TemperedDistribution.MemSobolev (-s) 2 μ.toTemperedDistribution := by
  apply TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  let f : Lp ℂ ⊤ (volume : Measure E) :=
    ((fourierMeasure μ).memLp_top).toLp (fourierMeasure μ)
  refine ⟨(memLp_besselWeight hs).toLp _ • f, ?_⟩
  rw [fourier_measure_distribution]
  exact (Lp.toTemperedDistribution_smul_eq (by fun_prop) (memLp_besselWeight hs) f).symm

theorem finite_measure_memHneg3 (μ : Measure (EuclideanSpace ℝ (Fin 4))) [IsFiniteMeasure μ] :
    TemperedDistribution.MemSobolev (-3) 2 μ.toTemperedDistribution := by
  apply finite_measure_memSobolev (s := 3) _ μ
  norm_num

end TamingCompatibility.EuclideanSobolev

end

end OAI
