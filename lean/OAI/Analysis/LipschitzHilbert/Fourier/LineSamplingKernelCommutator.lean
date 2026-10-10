import OAI.Analysis.LipschitzHilbert.Estimates.LipschitzCompositionCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionContinuity

namespace OAI

/-! The proved L2 operator commutator is the actual convolution/sampling
difference, with its squared integral bound. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineSamplingKernelCommutator (m : SchwartzMap ℝ ℂ) (u : ℝ → ℝ) (t : ℝ)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  lineConvolution (lineProjectionKernel m 1 (by norm_num))
      (fun z => f (lineSampling u t z)) y-
    lineConvolution (lineProjectionKernel m 1 (by norm_num)) f (lineSampling u t y)

theorem lineSamplingKernelCommutator_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hub : ∀ y, |u y|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    MemLp (lineSamplingKernelCommutator m u t f) 2 volume ∧
      (∫ y, ‖lineSamplingKernelCommutator m u t f y‖^2)≤
        (16*lineCommutatorNormConstant*A*|t|)^2*(∫ y, ‖f y‖^2) := by
  let K := lineProjectionKernel m 1 (by norm_num)
  let phi := lineSampling u t
  let F := fun y => f (phi y)
  let q := lineSchwartzProjection m 1 (by norm_num) f
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  have hphi : Measurable phi := (lineSampling_lipschitz u hu t ht').continuous.measurable
  have ha : AntilipschitzWith 2 phi := lineSampling_antilipschitz u hu t ht'
  have hF : MemLp F 2 volume := (line_memLp_comp phi hphi ha f f.continuous.measurable (f.memLp 2 volume)).1
  have hFm : Measurable F := f.continuous.measurable.comp hphi
  have hFbound (y : ℝ) : ‖F y‖≤SchwartzMap.seminorm ℝ 0 0 f := f.norm_le_seminorm ℝ _
  have hfirst := (lineConvolution_energy_bound K K.integrable K.continuous.measurable F hFm hF).1
  have hsecond := (line_memLp_comp phi hphi ha q q.continuous.measurable (q.memLp 2 volume)).1
  have hC : lineSamplingL2Path u hu t (f.toLp 2 volume)=hF.toLp F := by
    simp only [lineSamplingL2Path,dite_eq_left ht',lineCompositionL2_onSchwartz]
    rfl
  have hTC : lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))=
      hfirst.toLp (lineConvolution K F) := by
    rw [hC]
    exact lineL2Projection_on_bounded m 1 (by norm_num) F hFm hF _ hFbound
  have hCT : lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))=
      hsecond.toLp (q ∘ phi) := by
    rw [lineL2Projection_onSchwartz]
    simp only [lineSamplingL2Path,dite_eq_left ht',lineCompositionL2_onSchwartz]
    rfl
  have heq : lineSamplingKernelCommutator m u t f=lineConvolution K F-q ∘ phi := by
    funext y
    simp only [lineSamplingKernelCommutator,Pi.sub_apply,Function.comp_apply,q,
      lineSchwartzProjection_eq_convolution]
    rfl
  have hD : MemLp (lineSamplingKernelCommutator m u t f) 2 volume := by
    rw [heq]
    exact hfirst.sub hsecond
  have hid : lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))=
      hD.toLp (lineSamplingKernelCommutator m u t f) := by
    rw [hTC,hCT,←hfirst.toLp_sub hsecond]
    congr 1
    exact heq.symm
  have hb := lipschitzCompositionCommutator_L2 m A hA hm u hu hub t ht (f.toLp 2 volume)
  rw [hid] at hb
  refine ⟨hD,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hfNorm : ‖f.toLp 2 volume‖^2=∫ y, ‖f y‖^2 := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [mul_pow,memLp_toL2_norm_sq volume _ hD,hfNorm] at hs
  exact hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
