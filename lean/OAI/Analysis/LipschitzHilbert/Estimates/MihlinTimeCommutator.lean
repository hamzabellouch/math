import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingMihlin
import OAI.Analysis.LipschitzHilbert.Fourier.SharpVerticalCommutator

namespace OAI

/-! Uniform full-input multiplier commutators for the short Hilbert
integral. The first time moment cancels its singularity. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_eq_profile (m : SchwartzMap ℝ ℂ) :
    (lineProjectionKernel m 1 (by norm_num) : ℝ → ℂ)=verticalProfileKernel m 1 0 := by
  funext x
  rw [lineProjectionKernel_eq_scaled m 1 (by norm_num),scaledSchwartzKernel_apply]
  simp only [verticalProfileKernel,modulatedTimeKernel,zero_mul,Real.fourierChar.map_zero_eq_one,one_smul]

theorem mihlinTimeCommutator_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖)) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel m 1 0) u t f z else 0) 2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel m 1 0) u t f z else 0‖^2 ∂planeMeasure)≤
      (∫ t, |t| *‖K t‖)^2*(16*lineCommutatorNormConstant*A)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let B := (16*lineCommutatorNormConstant*A)^2*(∫ z, ‖f z‖^2 ∂planeMeasure)
  have hB : 0≤B := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hfiber (t : ℝ) (ht : |t|≤1/4) := verticalSamplingCommutator_mihlin_energy m A hA hm u hum hu hub t ht f
  simp only [lineProjectionKernel_eq_profile] at hfiber
  have hqi : Integrable (verticalProfileKernel m 1 0) := modulatedTimeKernel_integrable _ 1 0 (by norm_num)
  have hqm : Measurable (verticalProfileKernel m 1 0) := by
    rw [←lineProjectionKernel_eq_profile]
    exact (lineProjectionKernel m 1 (by norm_num)).continuous.measurable
  have hh := shortTimeAverage_energy K hKm hK1
    (fun p => verticalSamplingCommutator (verticalProfileKernel m 1 0) u p.1 f p.2)
    (verticalSamplingCommutator_joint_measurable _ hqm hqi u hum f) B hB
    (fun t ht => (hfiber t ht).1) (fun t ht => by
      have hh := (hfiber t ht).2
      convert hh using 1
      dsimp only [B]
      simp only [mul_pow,sq_abs]
      ring)
  exact ⟨hh.1,hh.2.trans_eq (by dsimp only [B]; ring)⟩

theorem sharpVerticalCommutator_mihlin_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (sharpVerticalCommutator m 1 0 epsilon R u f) 2 planeMeasure ∧
      (∫ z, ‖sharpVerticalCommutator m 1 0 epsilon R u f z‖^2 ∂planeMeasure)≤
        (32*lineCommutatorNormConstant*A*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  rw [sharpVerticalCommutator_eq m 1 0 epsilon R (by norm_num) he hR u hum f]
  have hh := mihlinTimeCommutator_energy m A hA hm u hum hu hub f
    (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_first_moment epsilon R he hR).1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp := pow_le_pow_left₀
    (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _))
    (sharpTimeKernel_first_moment epsilon R he hR).2 2
  have hb := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (sq_nonneg (16*lineCommutatorNormConstant*A))
      (integral_nonneg (μ:=planeMeasure) fun z => sq_nonneg ‖f z‖))
  convert hb using 1 <;> ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
