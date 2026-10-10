import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformContour
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinMean

namespace OAI

/-! At the critical line the angular Gamma quotient has modulus one.
Thus the actual translated Mellin kernel has one common integrable
weight, independent of height and of the retained frequency polynomial. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_metaplecticGamma_half (ℓ : ℤ) :
    Continuous (fun t : ℝ => metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hopen : IsOpen {s : ℂ | s.re < 5/6} := isOpen_lt Complex.continuous_re continuous_const
  have hmem : (1/2:ℂ)+(t:ℂ)*Complex.I ∈ {s : ℂ | s.re < 5/6} := by
    change ((1/2:ℂ)+(t:ℂ)*Complex.I).re < 5/6
    norm_num
  have hg : ContinuousAt (fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) t := by fun_prop
  exact ((differentiableOn_metaplecticGammaQuotient ℓ).differentiableAt
    (hopen.mem_nhds hmem)).continuousAt.comp
    (f := fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) hg

def metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ) (c : ℝ)
    (P : ℝ → ℂ) (τ t : ℝ) : ℂ :=
  mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
    metaplecticGammaQuotient ℓ ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
    mellinPhase (τ-t) c*P (τ-t)

lemma norm_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ) (c : ℝ)
    (P : ℝ → ℂ) (τ t : ℝ) :
    ‖metaplecticCriticalKernel ℓ W c P τ t‖ =
      ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*‖P (τ-t)‖ := by
  simp only [metaplecticCriticalKernel,norm_mul,norm_metaplecticGamma_half,
    mellinPhase_norm,mul_one]

lemma continuous_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2) := by
  have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
  have hg := (continuous_metaplecticGamma_half ℓ).comp
    (continuous_fst.sub continuous_snd)
  have hp : Continuous (fun z : ℝ × ℝ => mellinPhase (z.1-z.2) c) := by
    unfold mellinPhase
    fun_prop
  exact (((hm.comp (by fun_prop)).mul hg).mul hp).mul
    (hP.comp (continuous_fst.sub continuous_snd))

lemma metaplectic_mellin_half_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    Integrable (fun τ : ℝ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)) := by
  convert ((mellinVerticalSchwartz W hW hpos hsm (1/2)).integrable (μ := volume)) using 1
  ext τ
  rw [mellinVerticalSchwartz_apply]
  norm_num

lemma metaplecticCriticalKernel_integrable (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P)
    {B : ℝ} (hB : ∀ u, ‖P u‖ ≤ B) (t : ℝ) :
    Integrable (fun τ : ℝ => metaplecticCriticalKernel ℓ W c P τ t) := by
  have hx : Continuous (fun τ : ℝ => (τ,t)) := continuous_id.prodMk continuous_const
  have hc := Continuous.comp
    (f := fun τ : ℝ => (τ,t))
    (g := fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2)
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP) hx
  apply ((metaplectic_mellin_half_integrable W hW hpos hsm).norm.mul_const B).mono'
    hc.aestronglyMeasurable
  filter_upwards with τ
  dsimp only [Function.comp_def]
  rw [norm_metaplecticCriticalKernel]
  exact mul_le_mul_of_nonneg_left (hB (τ-t)) (_root_.norm_nonneg _)

/-- A uniform translated polynomial mean passes through the literal
critical-line Gamma kernel with the L1 mass of the actual Mellin transform. -/
theorem metaplectic_critical_kernel_mean (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) (P : ℝ → ℂ) (hP : Continuous P)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ τ : ℝ, (∫ t in T..2*T, ‖P (τ-t)‖)/T ≤ B) :
    (∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ t‖)/T ≤
      B*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  have hm := (metaplectic_mellin_half_integrable W hW hpos hsm).norm
  have hb (τ : ℝ) :
      (∫ t in T..2*T, ‖metaplecticCriticalKernel ℓ W c P τ t‖) ≤
        (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖ := by
    simp_rw [norm_metaplecticCriticalKernel]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*(B*T) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp (hmean τ)) (_root_.norm_nonneg _)
      _ = _ := by ring
  have hi := integral_height_norm_le
    (fun z => metaplecticCriticalKernel ℓ W c P z.1 z.2)
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP)
    (show T ≤ 2*T by linarith)
    (fun τ => (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)
    (hm.const_mul (B*T)) hb
  rw [integral_const_mul] at hi
  apply (div_le_iff₀ hT).mpr
  nlinarith only [hi]

end CubicFirstMoment

end

end OAI
