import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingKernelCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingCommutator
import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSlices

namespace OAI

/-! Fiberwise Mihlin control of the actual planar sampling commutator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def scalarVerticalSlice (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (verticalLine_temperate x) (verticalLine_antilipschitz x) f

@[simp] theorem scalarVerticalSlice_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    scalarVerticalSlice f x y=f (x,y) := rfl

theorem verticalSamplingCommutator_fiber (m : SchwartzMap ℝ ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f (x,y)=
      lineSamplingKernelCommutator m (fun z => u (x,z)) t (scalarVerticalSlice f (x-t)) y := rfl

theorem verticalSamplingCommutator_mihlin_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f z‖^2 ∂planeMeasure)≤
        (16*lineCommutatorNormConstant*A*|t|)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let K := lineProjectionKernel m 1 (by norm_num)
  let D := verticalSamplingCommutator K u t f
  let c := (16*lineCommutatorNormConstant*A*|t|)^2
  have hline (x : ℝ) := lineSamplingKernelCommutator_energy m A hA hm
    (fun y => u (x,y)) (hu x) (fun y => hub (x,y)) t ht (scalarVerticalSlice f (x-t))
  have hDx (x : ℝ) : MemLp (fun y => D (x,y)) 2 volume ∧
      (∫ y, ‖D (x,y)‖^2)≤c*(∫ y, ‖f (x-t,y)‖^2) := by
    simpa only [D,K,verticalSamplingCommutator_fiber,scalarVerticalSlice_apply] using hline x
  have hDm : Measurable D := by
    have hsample : Measurable (sampledFunction u t f) :=
      f.continuous.measurable.comp (by fun_prop)
    exact (verticalConvolution_measurable K K.continuous.measurable _ hsample).sub
      ((verticalConvolution_measurable K K.continuous.measurable f f.continuous.measurable).comp (by fun_prop))
  have hi : Integrable (fun z => ‖f z‖^2) planeMeasure :=
    (f.memLp 2 planeMeasure).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hinput : Integrable (fun x : ℝ => ∫ y : ℝ, ‖f (x-t,y)‖^2) :=
    hi.integral_prod_left.comp_sub_right t
  have hDi : Integrable (fun z => ‖D z‖^2) planeMeasure := by
    apply (integrable_prod_iff (hDm.norm.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun x => (hDx x).1.integrable_norm_pow (by decide : (2:ℕ)≠0)
    · simp only [Real.norm_of_nonneg (sq_nonneg _)]
      apply (hinput.const_mul c).mono'
        (hDm.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (integral_nonneg fun y => sq_nonneg ‖D (x,y)‖)]
        exact (hDx x).2
  refine ⟨(memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).mpr hDi,?_⟩
  change (∫ z, ‖D z‖^2 ∂planeMeasure)≤c*(∫ z, ‖f z‖^2 ∂planeMeasure)
  rw [integral_prod _ hDi]
  calc
    _ ≤ ∫ x, c*(∫ y, ‖f (x-t,y)‖^2) :=
      integral_mono hDi.integral_prod_left (hinput.const_mul c) (fun x => (hDx x).2)
    _ = c*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      congr 1
      calc
        (∫ x : ℝ, ∫ y : ℝ, ‖f (x-t,y)‖^2) = ∫ x : ℝ, ∫ y : ℝ, ‖f (x,y)‖^2 :=
          integral_sub_right_eq_self (fun x : ℝ => ∫ y : ℝ, ‖f (x,y)‖^2) t
        _ = _ := (integral_prod _ hi).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
