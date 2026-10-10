import OAI.Analysis.LipschitzHilbert.Fourier.LineDyadicSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.LocalizedMihlinProfile

namespace OAI

/-! Exact localized line multipliers and the scale-cancelling first-moment
bound used in the low/high commutator estimate. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def localizedLineSymbol (m : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V) : SchwartzMap ℝ ℂ :=
  localizedMihlinProfile m dyadicCommutatorCutoff V⁻¹ (inv_ne_zero hV.ne')

theorem localizedLineProjection_eq (m f : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V)
    (hcut : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 f) eta=(𝓕 f) eta) :
    lineSchwartzProjection (localizedLineSymbol m V hV) V hV.ne' f=
      lineSchwartzProjection m 1 (by norm_num) f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection (localizedLineSymbol m V hV) V hV.ne' f)) eta=
    (𝓕 (lineSchwartzProjection m 1 (by norm_num) f)) eta
  rw [lineSchwartzProjection_fourier,lineSchwartzProjection_fourier]
  simp only [localizedLineSymbol,localizedMihlinProfile_apply,one_mul]
  have he : V⁻¹*(V*eta)=eta := by field_simp
  rw [he,mul_assoc,hcut]

theorem localizedLineKernel_firstMoment (m : SchwartzMap ℝ ℂ) (V A : ℝ) (hV : 0<V) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A) :
    (∫ t, |t| *‖lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne' t‖)≤
      V*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff := by
  rw [lineProjectionKernel_moment1 _ V hV]
  have hh := localizedMihlinProfile_kernel_firstMoment m dyadicCommutatorCutoff V⁻¹ A
    (inv_pos.mpr hV) hA hm dyadicCommutatorCutoff_away_zero dyadicCommutatorCutoff_bounded_support
  exact (mul_le_mul_of_nonneg_left hh hV.le).trans_eq (by ring)

theorem localizedLineCommutator_derivative_energy (m h : SchwartzMap ℝ ℂ)
    (V A : ℝ) (hV : 0<V) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B)
    (L R : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hband : ∀ eta, (𝓕 h) eta≠0 → |eta|≤R) :
    let K := lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne'
    MemLp (lineMultiplicationCommutator K b (schwartzDerivative 1 h)) 2 volume ∧
      (∫ x, ‖lineMultiplicationCommutator K b (schwartzDerivative 1 h) x‖^2)≤
        (L*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff*V*(2*Real.pi*R))^2*
          (∫ x, ‖h x‖^2) := by
  intro K
  have hc := lineMultiplicationCommutator_energy K (schwartzDerivative 1 h) b hbm B hB hb L hLip
  have hmom := localizedLineKernel_firstMoment m V A hV hA hm
  have hpos := localizedKernelFirstMomentConstant_nonneg dyadicCommutatorCutoff
  have hs := pow_le_pow_left₀ (integral_nonneg (fun _ => by positivity)) hmom 2
  have hbnd := line_bernstein_energy h R hband
  refine ⟨hc.1,?_⟩
  calc
    _ ≤ L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖schwartzDerivative 1 h x‖^2) := hc.2
    _ ≤ L^2*(V*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff)^2*
        ((2*Real.pi*R)^2*(∫ x, ‖h x‖^2)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hs (sq_nonneg L)) hbnd
        (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
