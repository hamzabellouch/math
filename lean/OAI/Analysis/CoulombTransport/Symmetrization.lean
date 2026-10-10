import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.Cyclic

/-- The cyclic rotation of the three particles. -/
def rotate : Triple ≃ᵐ Triple where
  toFun t := (t.2.1, (t.2.2, t.1))
  invFun t := (t.2.2, (t.1, t.2.1))
  left_inv t := by rfl
  right_inv t := by rfl
  measurable_toFun := measurable_snd.fst.prodMk
    (measurable_snd.snd.prodMk measurable_fst)
  measurable_invFun := measurable_snd.snd.prodMk
    (measurable_fst.prodMk measurable_snd.fst)

/-- Averaging over the cyclic group already gives identical coordinate marginals. -/
def symmetrize (pi : Measure Triple) : Measure Triple :=
  (3 : ℝ≥0∞)⁻¹ • (pi + Measure.map rotate pi + Measure.map rotate.symm pi)

/-- The common marginal of the cyclic average. -/
def averageMarginal (pi : Measure Triple) : Measure E3 :=
  (3 : ℝ≥0∞)⁻¹ •
    (Measure.map tripleFst pi + Measure.map tripleSnd pi + Measure.map tripleThd pi)

private theorem measurable_fst₃ : Measurable tripleFst := measurable_fst
private theorem measurable_snd₃ : Measurable tripleSnd := measurable_snd.fst
private theorem measurable_thd₃ : Measurable tripleThd := measurable_snd.snd

theorem map_fst_symmetrize (pi : Measure Triple) :
    Measure.map tripleFst (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul _ measurable_fst₃.aemeasurable,
    Measure.map_add _ _ measurable_fst₃,
    Measure.map_map measurable_fst₃ rotate.measurable,
    Measure.map_map measurable_fst₃ rotate.symm.measurable]
  rfl

theorem map_snd_symmetrize (pi : Measure Triple) :
    Measure.map tripleSnd (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul _ measurable_snd₃.aemeasurable,
    Measure.map_add _ _ measurable_snd₃,
    Measure.map_map measurable_snd₃ rotate.measurable,
    Measure.map_map measurable_snd₃ rotate.symm.measurable]
  change (3 : ℝ≥0∞)⁻¹ •
      (Measure.map tripleSnd pi + Measure.map tripleThd pi + Measure.map tripleFst pi) = _
  ac_rfl

theorem map_thd_symmetrize (pi : Measure Triple) :
    Measure.map tripleThd (symmetrize pi) = averageMarginal pi := by
  simp only [symmetrize, averageMarginal, Measure.map_smul _ measurable_thd₃.aemeasurable,
    Measure.map_add _ _ measurable_thd₃,
    Measure.map_map measurable_thd₃ rotate.measurable,
    Measure.map_map measurable_thd₃ rotate.symm.measurable]
  change (3 : ℝ≥0∞)⁻¹ •
      (Measure.map tripleThd pi + Measure.map tripleFst pi + Measure.map tripleSnd pi) = _
  ac_rfl

theorem symmetrize_probability (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsProbabilityMeasure (symmetrize pi) := by
  constructor
  simp [symmetrize, Measure.map_apply rotate.measurable,
    Measure.map_apply rotate.symm.measurable]
  rw [← two_mul, ← add_one_mul]
  norm_num only [Nat.reduceAdd]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem symmetrize_isThreeCoupling (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsThreeCoupling (averageMarginal pi) (symmetrize pi) :=
  ⟨symmetrize_probability pi, map_fst_symmetrize pi,
    map_snd_symmetrize pi, map_thd_symmetrize pi⟩

/-- A cyclically invariant property holding almost everywhere survives symmetrization.
No measurability hypothesis on the property is necessary. -/
theorem ae_symmetrize_of_rotate_invariant (pi : Measure Triple) {P : Triple → Prop}
    (hP : ∀ᵐ t ∂pi, P t) (hrotate : ∀ t, P (rotate t) ↔ P t) :
    ∀ᵐ t ∂symmetrize pi, P t := by
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨hP, rotate.measurableEmbedding.ae_map_iff.mpr ?_⟩,
    rotate.symm.measurableEmbedding.ae_map_iff.mpr ?_⟩
  · exact hP.mono fun t ht => (hrotate t).mpr ht
  · exact hP.mono fun t ht => (hrotate (rotate.symm t)).mp (by simpa using ht)

theorem averageMarginal_probability (pi : Measure Triple) [IsProbabilityMeasure pi] :
    IsProbabilityMeasure (averageMarginal pi) := by
  have := symmetrize_probability pi
  rw [← map_fst_symmetrize pi]
  infer_instance

private theorem invDistance_comm (x y : E3) : invDistance x y = invDistance y x := by
  simp only [invDistance, norm_sub_rev]

theorem cost_rotate (t : Triple) : coulombCost (rotate t) = coulombCost t := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, rotate,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [invDistance_comm t.2.1 t.1, invDistance_comm t.2.2 t.1]
  ac_rfl

theorem cost_rotate_symm (t : Triple) : coulombCost (rotate.symm t) = coulombCost t := by
  simpa using (cost_rotate (rotate.symm t)).symm

theorem lintegral_symmetrize (pi : Measure Triple) :
    (∫⁻ t, coulombCost t ∂symmetrize pi) = ∫⁻ t, coulombCost t ∂pi := by
  rw [symmetrize, lintegral_smul_measure, lintegral_add_measure,
    lintegral_add_measure, lintegral_map_equiv, lintegral_map_equiv]
  simp only [cost_rotate, cost_rotate_symm, smul_eq_mul]
  rw [← two_mul, ← add_one_mul]
  norm_num only [Nat.reduceAdd]
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

end Problem356.Cyclic

end

end OAI
