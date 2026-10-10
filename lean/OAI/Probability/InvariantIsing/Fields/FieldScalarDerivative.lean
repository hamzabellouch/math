import OAI.Probability.InvariantIsing.Fields.FieldSpinDerivative
import OAI.Probability.InvariantIsing.Fields.FieldScalarChain

namespace OAI

/-! The actual backward conditional spin mean is the spatial derivative
of the scalar Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma hasDerivAt_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {K : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K)
    (hder : ∀ z, HasDerivAt F (a z) z) (z : ℝ) :
    HasDerivAt (fieldScalarValue L F) (fieldScalarMean L F a z) z := by
  induction L generalizing z with
  | nil => exact hder z
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    exact hasDerivAt_gaussianOperator av.1 av.2 hval.1 hval.2 hmean.1 hK hmean.2
      (ih htail) z

lemma hasDerivAt_fieldScalarLogCosh (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
      (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth hm
    zero_le_one field_abs_tanh_le_one
  intro x
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

end InvariantIsing

end

end OAI
