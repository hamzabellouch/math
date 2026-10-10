import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! # Fixed linear coordinates preserve subexponential volume rates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V] [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [Measure.IsAddHaarMeasure (volume : Measure W)]

omit [FiniteDimensional ℝ W] in
theorem linear_equiv_volume_image_factor (e : V ≃L[ℝ] W) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : Set V,
      volume (e '' S) = ENNReal.ofReal c * volume S := by
  let c := Measure.addHaarScalarFactor (Measure.map e.symm volume) (volume : Measure V)
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c, hc, ?_⟩
  intro S
  have hm := Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.map e.symm volume) (volume : Measure V)
  have he := congrArg (fun μ : Measure V => μ S) hm
  change (Measure.map e.toHomeomorph.symm volume) S = _ at he
  rw [e.toHomeomorph.symm.measurableEmbedding.map_apply,
    e.toHomeomorph.preimage_symm, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at he
  simpa only [c, ENNReal.ofReal_coe_nnreal, ContinuousLinearEquiv.coe_toHomeomorph] using he

omit [FiniteDimensional ℝ W] in
theorem HasSubexponentialLowerBoundSeq.linear_image {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (e : V ≃L[ℝ] W)
    {A : ℕ → Set V}
    (hA : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (e '' A r)).toReal) := by
  obtain ⟨c, hc, hm⟩ := linear_equiv_volume_image_factor e
  have he (r : ℕ) : (volume (e '' A r)).toReal = c * (volume (A r)).toReal := by
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  simpa only [he] using (sequence_subexponential_lower_const hscale hc).mul hA

end PolycyclicRecognition

end

end OAI
