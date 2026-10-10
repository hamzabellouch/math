import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRootLoss
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockTerminalLoss

namespace OAI

/-! Exact bias cancellation on a constrained block and identification of
the unrestricted block with the average scalar field functional. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def biasedConstrainedBlockValue {N : ℕ} (S : Finset (Spin N)) (h : FieldStep)
    (b : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut)
    (fieldStepVariance h) z
    ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) -
      h.height (Fin.last h.depth) / 2

lemma fieldValue_gaussian_integral (h : FieldStep) (b : ℝ) :
    (∫ z, fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) z
      ∂gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))) =
      fieldValue h b + h.height (Fin.last h.depth) / 2 := by
  have he := gaussianOperator_eq_gaussian_integral (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).1 b
  change gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y))) b = _ at he
  rw [fieldValue_root]
  linarith [he]

theorem biasedConstrainedBlockValue_univ {N : ℕ} (hN : 0 < N) (h : FieldStep) (b : Fin N → ℝ) :
    biasedConstrainedBlockValue Finset.univ h b = (N : ℝ)⁻¹ * ∑ i, fieldValue h (b i) := by
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have hrec : restrictedFieldRecursion (Finset.univ : Finset (Spin N)) h.depth
      (chainExponent h.cut) (fieldStepVariance h) = fun z => ∑ i,
        fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i) := by
    funext z
    simpa only [fieldStepIncrements] using restrictedFieldRecursion_univ h.depth
      (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1) z
  have hreg := fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth
  have hi (i : Fin N) : Integrable (fun z : Fin N → ℝ =>
      fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i))
      (Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))) :=
    (measurePreserving_eval _ i).integrable_comp_of_integrable
      (field_gaussian_linear_integrable _ (b i) hreg.1 hreg.2)
  rw [biasedConstrainedBlockValue, hrec, integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin N) : (∫ z : Fin N → ℝ,
      fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i)
      ∂Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))) =
      fieldValue h (b i) + h.height (Fin.last h.depth) / 2 := by
    rw [integral_comp_eval (μ := fun j : Fin N =>
      gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0))) (i := i) hreg.1.aestronglyMeasurable]
    exact fieldValue_gaussian_integral h (b i)
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem biasedConstrainedBlockValue_group {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ) (h : FieldStep) :
    biasedConstrainedBlockValue (spinGroupSlice group k) h (fun i => bias (group i)) =
      constrainedBlockValue (spinGroupSlice group k) h +
        (N : ℝ)⁻¹ * spinGroupFieldConstant group k bias := by
  let S := spinGroupSlice group k
  let F := restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h)
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have hreg := restrictedFieldRecursion_regular hN S (spinGroupSlice_nonempty group k hk)
    h.depth (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1)
  have he : (∫ z, F z ∂Measure.pi (fun i => gaussianReal (bias (group i))
      (NNReal.mk (h.height 0) (h.nonneg 0)))) =
      ∫ z, F z + spinGroupFieldConstant group k bias
        ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) := by
    rw [← (vectorGaussian_shift _ (fun i => bias (group i))).map_eq,
      integral_map (show AEMeasurable (fun z : Fin N → ℝ => (fun i => bias (group i)) + z)
        (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) from
          (measurable_const.add measurable_id).aemeasurable) hreg.1.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change F ((fun i => bias (group i)) + z) = _
    rw [add_comm]
    exact restrictedFieldRecursion_group_bias hN group k hk bias _ _ _
      (fun i hi => (hb.1 i hi).1) z
  change (N : ℝ)⁻¹ * (∫ z, F z ∂_) - _ = (N : ℝ)⁻¹ * (∫ z, F z ∂_) - _ + _
  rw [he, integral_add (constrainedBlockValue_root_integrable hN S
    (spinGroupSlice_nonempty group k hk) h) (integrable_const _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

end InvariantIsing

end

end OAI
