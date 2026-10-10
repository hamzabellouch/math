import OAI.Probability.InvariantIsing.Fields.FieldTailMgf
import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverseConvex

namespace OAI

/-! The canonical terminal field has a depth-independent second moment,
controlled by the initial bias and the final covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma fieldTailVariance_total (h : FieldStep) :
    h.height 0 + fieldTailVariance (scalarFieldIncrements h) =
      h.height (Fin.last h.depth) := by
  have hs := fieldIncrement_sum h
  rw [Fin.sum_univ_succ] at hs
  have htail : fieldTailVariance (scalarFieldIncrements h) =
      ∑ i : Fin h.depth, (fieldIncrement h i.succ).2 := by
    simp only [fieldTailVariance, scalarFieldIncrements, List.map_ofFn,
      Function.comp_apply, NNReal.coe_mk, List.sum_ofFn]
  rw [htail]
  simpa [fieldIncrement] using hs

theorem fieldCanonicalEndpointLaw_mgf (h : FieldStep) (b t : ℝ) :
    Integrable (fun y => Real.exp (t * y)) (fieldCanonicalEndpointLaw h b) ∧
      (∫ y, Real.exp (t * y) ∂fieldCanonicalEndpointLaw h b) ≤
        Real.exp (t * b + (t ^ 2 / 2 + |t|) * h.height (Fin.last h.depth)) := by
  let L := scalarFieldIncrements h
  have hL := scalarFieldIncrements_positive h
  have hB := scalarFieldIncrements_exponent_le_one h
  have hreg := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let root : ℝ≥0 := ⟨h.height 0, h.nonneg 0⟩
  let κ := fieldTransitionKernel 0 root
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hreg.1
  have hκ (z : ℝ) := And.intro
    (fieldTransitionKernel_integrable_exp root z 0 t _ hreg.1 hreg.2)
    (fieldScalarTransition_mgf L hL root z 0 t le_rfl zero_le_one)
  have he := kernel_exp_bound_comp κ (fieldTailEndpointKernel L hL) t
    ((t ^ 2 / 2 + |t|) * root) ((t ^ 2 / 2 + |t|) * fieldTailVariance L)
    hκ (fieldTailEndpointKernel_mgf L hL hB t) b
  have hlaw : (fieldTailEndpointKernel L hL ∘ₖ κ) b = fieldCanonicalEndpointLaw h b := by
    rw [Kernel.comp_apply]
    dsimp only [κ]
    rw [fieldTransitionKernel_zero _ _ hreg.1 hreg.2]
    rfl
  rw [hlaw] at he
  refine ⟨he.1, he.2.trans_eq ?_⟩
  congr 1
  change t * b + (t ^ 2 / 2 + |t|) * h.height 0 +
    (t ^ 2 / 2 + |t|) * fieldTailVariance (scalarFieldIncrements h) = _
  calc
    _ = t * b + (t ^ 2 / 2 + |t|) *
        (h.height 0 + fieldTailVariance (scalarFieldIncrements h)) := by ring
    _ = _ := by rw [fieldTailVariance_total]

lemma sq_le_exp_two_add (x : ℝ) : x ^ 2 ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
  have ha : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have hs := (sq_le_sq₀ (abs_nonneg x) (Real.exp_pos _).le).mpr ha
  rw [sq_abs] at hs
  rw [show (Real.exp |x|) ^ 2 = Real.exp (|x| + |x|) by
    rw [pow_two, Real.exp_add]] at hs
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, show x + x = 2 * x by ring] at hs
    linarith [Real.exp_pos (-2 * x)]
  · rw [abs_of_nonpos (le_of_not_ge hx), show -x + -x = -2 * x by ring] at hs
    linarith [Real.exp_pos (2 * x)]

theorem fieldCanonicalEndpointLaw_second_moment (h : FieldStep) (b : ℝ) :
    Integrable (fun y : ℝ => y ^ 2) (fieldCanonicalEndpointLaw h b) ∧
      (∫ y, y ^ 2 ∂fieldCanonicalEndpointLaw h b) ≤
        Real.exp (2 * b + 4 * h.height (Fin.last h.depth)) +
          Real.exp (-2 * b + 4 * h.height (Fin.last h.depth)) := by
  have hp := fieldCanonicalEndpointLaw_mgf h b 2
  have hn := fieldCanonicalEndpointLaw_mgf h b (-2)
  have hi : Integrable (fun y : ℝ => y ^ 2) (fieldCanonicalEndpointLaw h b) := by
    apply (hp.1.add hn.1).mono' (by fun_prop)
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_exp_two_add y)
  refine ⟨hi, ?_⟩
  have hle := integral_mono hi (hp.1.add hn.1) sq_le_exp_two_add
  simp only [Pi.add_apply] at hle
  rw [integral_add hp.1 hn.1] at hle
  norm_num at hp hn
  have hn' : (∫ y, Real.exp (-2 * y) ∂fieldCanonicalEndpointLaw h b) ≤
      Real.exp (-2 * b + 4 * h.height (Fin.last h.depth)) := by
    simpa only [neg_mul] using hn.2
  exact hle.trans (add_le_add hp.2 hn')

end InvariantIsing

end

end OAI
