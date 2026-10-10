import OAI.Analysis.Triangular.Energy.Basic

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/- Necessary analytic transfer from §2. We use finite positive measures for the
   comparison form; the eventual quadratic inequality also handles real signed
   linear combinations, without imposing spacing on the configuration. -/
def phase (w x : Plane) : ℂ := Complex.exp ((2 * Real.pi * ⟪w, x⟫ : ℝ) * I)
def pattern (μ : Measure Plane) (w : Plane) : ℂ :=
  charFun μ ((2 * Real.pi) • w)

def kernelForm (f : Plane → ℂ) (μ ν : Measure Plane) : ℂ :=
  ∫ xy : Plane × Plane, f (xy.1 - xy.2) ∂(μ.prod ν)

lemma phase_continuous : Continuous (fun wx : Plane × Plane => phase wx.1 wx.2) := by
  unfold phase
  fun_prop

lemma phase_norm (w x : Plane) : ‖phase w x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_sub (w x y : Plane) :
    phase w (x-y) = phase w x * conj (phase w y) := by
  simp only [phase, inner_sub_right, Complex.ofReal_mul, Complex.ofReal_sub,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  ring

lemma pattern_eq (μ : Measure Plane) (w : Plane) :
    pattern μ w = ∫ x, phase w x ∂μ := by
  simp only [pattern, charFun_apply, phase, inner_smul_right]
  congr 1
  funext x
  rw [real_inner_comm x w]

lemma pattern_continuous (μ : Measure Plane) [IsFiniteMeasure μ] :
    Continuous (pattern μ) := by
  unfold pattern
  fun_prop

lemma pattern_bound (μ : Measure Plane) (w : Plane) :
    ‖pattern μ w‖ ≤ μ.real Set.univ := norm_charFun_le _

lemma spectral_integrable (h : Plane → ℂ) (hh : Integrable h)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun w => h w * pattern μ w * conj (pattern ν w)) := by
  exact (hh.mul_bdd (pattern_continuous μ).aestronglyMeasurable
    (Eventually.of_forall (pattern_bound μ))).mul_bdd
    ((pattern_continuous ν).star.aestronglyMeasurable)
    (Eventually.of_forall fun w => by simpa using pattern_bound ν w)

lemma integral_phase_sub (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (w : Plane) :
    (∫ xy : Plane × Plane, phase w (xy.1 - xy.2) ∂(μ.prod ν)) =
      pattern μ w * conj (pattern ν w) := by
  simp_rw [phase_sub]
  rw [integral_prod_mul (phase w) (fun y => conj (phase w y)),
    integral_conj, ← pattern_eq, ← pattern_eq]

lemma kernelForm_spectral (f : Plane → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelForm f μ ν = ∫ w, 𝓕 f w * pattern μ w * conj (pattern ν w) := by
  have hm : AEStronglyMeasurable
      (fun p : (Plane × Plane) × Plane => phase p.2 (p.1.1 - p.1.2) * 𝓕 f p.2)
      ((μ.prod ν).prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (phase_continuous.comp (continuous_snd.prodMk
        (continuous_fst.fst.sub continuous_fst.snd))).aestronglyMeasurable
    · exact hF.aestronglyMeasurable.comp_snd
  have hint : Integrable
      (fun p : (Plane × Plane) × Plane => phase p.2 (p.1.1 - p.1.2) * 𝓕 f p.2)
      ((μ.prod ν).prod volume) := by
    apply (hF.norm.comp_snd (μ.prod ν)).mono' hm
    exact Eventually.of_forall fun p => by simp [phase_norm]
  have hp (x : Plane) : f x = ∫ w, phase w x * 𝓕 f w := by
    calc
      f x = 𝓕⁻ (𝓕 f) x := (congrFun (hc.fourierInv_fourier_eq hf hF) x).symm
      _ = _ := by rw [Real.fourierInv_eq']; rfl
  unfold kernelForm
  simp_rw [hp]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [integral_mul_const, integral_phase_sub]
    ring

lemma integral_reC {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  exact (integral_re hf).symm

lemma integral_sub_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B C D : α → ℂ} (hA : Integrable A μ) (hB : Integrable B μ)
    (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ x, A x - B x - C x + D x ∂μ) =
      (∫ x, A x ∂μ) - (∫ x, B x ∂μ) - (∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
  calc
    _ = (∫ x, A x - B x - C x ∂μ) + ∫ x, D x ∂μ := integral_add ((hA.sub hB).sub hC) hD
    _ = ((∫ x, A x - B x ∂μ) - ∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
      exact congrArg (fun z => z + ∫ x, D x ∂μ) (integral_sub (hA.sub hB) hC)
    _ = _ := by rw [integral_sub hA hB]

lemma spectral_re_nonneg (z p : ℂ) (hz : z.im = 0) (hn : 0 ≤ z.re) :
    0 ≤ (z * p * conj p).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hz,
    zero_mul, sub_zero]
  nlinarith [sq_nonneg p.re, sq_nonneg p.im]

lemma kernelForm_diag_re_nonneg (f : Plane → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hreal : ∀ w, (𝓕 f w).im = 0) (hpos : ∀ w, 0 ≤ (𝓕 f w).re)
    (μ : Measure Plane) [IsFiniteMeasure μ] : 0 ≤ (kernelForm f μ μ).re := by
  rw [kernelForm_spectral f hc hf hF, integral_reC (spectral_integrable _ hF μ μ)]
  exact integral_nonneg fun w => spectral_re_nonneg _ _ (hreal w) (hpos w)

lemma kernelForm_comparison (f : Plane → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hreal : ∀ w, (𝓕 f w).im = 0) (hpos : ∀ w, 0 ≤ (𝓕 f w).re)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    2 * (kernelForm f μ ν).re - (kernelForm f ν ν).re ≤ (kernelForm f μ μ).re := by
  have hsym : (kernelForm f ν μ).re = (kernelForm f μ ν).re := by
    rw [kernelForm_spectral f hc hf hF, kernelForm_spectral f hc hf hF,
      integral_reC (spectral_integrable _ hF ν μ),
      integral_reC (spectral_integrable _ hF μ ν)]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      hreal w, zero_mul, sub_zero]
    ring
  have hn : 0 ≤ (kernelForm f μ μ - kernelForm f μ ν - kernelForm f ν μ +
      kernelForm f ν ν).re := by
    simp only [kernelForm_spectral f hc hf hF]
    rw [← integral_sub_sub_add (spectral_integrable _ hF μ μ) (spectral_integrable _ hF μ ν)
      (spectral_integrable _ hF ν μ) (spectral_integrable _ hF ν ν)]
    have hh := integral_reC ((((spectral_integrable _ hF μ μ).sub (spectral_integrable _ hF μ ν)).sub
        (spectral_integrable _ hF ν μ)).add (spectral_integrable _ hF ν ν))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    rw [hh]
    apply integral_nonneg
    intro w
    change (0 : ℝ) ≤ (𝓕 f w * pattern μ w * conj (pattern μ w) -
        𝓕 f w * pattern μ w * conj (pattern ν w) -
        𝓕 f w * pattern ν w * conj (pattern μ w) +
        𝓕 f w * pattern ν w * conj (pattern ν w)).re
    have hp := spectral_re_nonneg (𝓕 f w) (pattern μ w - pattern ν w) (hreal w) (hpos w)
    have he : 𝓕 f w * pattern μ w * conj (pattern μ w) -
        𝓕 f w * pattern μ w * conj (pattern ν w) -
        𝓕 f w * pattern ν w * conj (pattern μ w) +
        𝓕 f w * pattern ν w * conj (pattern ν w) =
        𝓕 f w * (pattern μ w - pattern ν w) * conj (pattern μ w - pattern ν w) := by
      simp only [map_sub]
      ring
    rw [he]
    exact hp
  simp only [Complex.sub_re, Complex.add_re, hsym] at hn
  linarith
end TriangularUniversal
end

end OAI
