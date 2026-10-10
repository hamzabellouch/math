import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.ScalarSampling
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

namespace OAI

open MeasureTheory
namespace Invariant233.CircleParameterData

theorem kernel_eq_manuscriptKernel (m : ℕ) (z v : ℝ)
    (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    kernel m z v = ScalarSampling.manuscriptKernel m z v := by
  have he : Int.fract v = v := Int.fract_eq_self.mpr hv
  simp only [kernel, kernelWidth, delta, ScalarSampling.manuscriptKernel,
    ScalarSampling.circleKernel, ScalarSampling.rawKernel, ScalarSampling.delta, he,
    Set.indicator_apply, Set.mem_Ioo, one_div]
  split_ifs <;> simp_all

theorem starting_kernel_fract (m : ℕ) (z v : ℝ) :
    orientedKernel false m z (Int.fract v) =
      ScalarSampling.manuscriptKernel m z (Int.fract v) := by
  simpa only [orientedKernel, Bool.false_eq_true, ↓reduceIte] using
    kernel_eq_manuscriptKernel m z (Int.fract v)
      ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩

theorem endpoint_kernel_fract (m : ℕ) (z v : ℝ) :
    orientedKernel true m z (Int.fract v) =
      ScalarSampling.manuscriptEndpointKernel m z (Int.fract v) := by
  simpa only [orientedKernel, ↓reduceIte, ScalarSampling.manuscriptEndpointKernel] using
    kernel_eq_manuscriptKernel m (z - Int.fract v) (Int.fract v)
      ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩

theorem measurable_rep : Measurable rep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable

theorem measurable_coordinate (p : CircleParameterData) (i : ℕ) :
    Measurable (p.coordinate i) := by
  exact measurable_rep.comp (continuous_nsmul (p.q i)).measurable

theorem measurable_kernel (m : ℕ) (v : ℝ) : Measurable (fun z => kernel m z v) := by
  have hd : Measurable delta := measurable_fract.min (measurable_const.sub measurable_fract)
  unfold kernel
  apply Measurable.ite
  · exact (measurableSet_le measurable_const hd).inter
      ((MeasurableSet.const (0 < v)).inter
        (measurableSet_lt measurable_const (measurable_const.mul hd)))
  · exact measurable_const.div (measurable_const.mul hd)
  · exact measurable_const

theorem measurable_orientedKernel (endpoint : Bool) (m : ℕ) (v : ℝ) :
    Measurable (fun z => orientedKernel endpoint m z v) := by
  cases endpoint
  · exact measurable_kernel m v
  · exact (measurable_kernel m v).comp (measurable_id.sub_const v)

theorem measurable_samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) : Measurable (p.samplingAverage θ j r endpoint) := by
  unfold samplingAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_orientedKernel endpoint (p.m j)
    (Int.fract ((n : ℝ) * p.alpha θ i))).comp (p.measurable_coordinate i)

end Invariant233.CircleParameterData

end OAI
