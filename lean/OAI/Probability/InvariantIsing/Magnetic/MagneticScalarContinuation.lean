import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLevels

namespace OAI

/-! The literal conditional squared means of the finite Ising recursion
have bounded spatial derivatives through order three. The ordinary root
Gaussian is retained in the statement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticLogCoshMeanJet (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1) :
    MagneticContinuationJet := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hf : Measurable fieldLogCoshFourth := by unfold fieldLogCoshFourth; fun_prop
  have hM := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hQ := fieldScalarLogCoshSecond_regular L hL
  have hR := fieldScalarThird_regular L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  have hS := fieldScalarFourth_regular L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) hf zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
  refine {
    value := fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh
    first := fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2)
    second := fieldScalarThird L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2) (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2)
    third := fieldScalarFourth L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2) (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2)
      fieldLogCoshFourth
    mValue := hM.1
    mFirst := hQ.1
    mSecond := hR.1
    mThird := hS.1
    bValue := ⟨1, zero_le_one, hM.2⟩
    bFirst := ⟨_, (abs_nonneg _).trans (hQ.2 0), hQ.2⟩
    bSecond := ⟨_, (abs_nonneg _).trans (hR.2 0), hR.2⟩
    bThird := hS.2
    dValue := hasDerivAt_fieldScalarLogCoshMean L hL
    dFirst := hasDerivAt_fieldScalarLogCoshSecond L hL
    dSecond := hasDerivAt_fieldScalarLogCoshThird L hL }

theorem fieldScalarSquares_has_bounded_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    ∃ J : MagneticContinuationJet,
      J.value = fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i := by
  induction L with
  | nil =>
    exact ⟨(magneticLogCoshMeanJet [] hL).square, rfl⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨(magneticLogCoshMeanJet (av :: L) hL).square, rfl⟩
    · obtain ⟨J, hJ⟩ := ih ht j
      have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      let P := magneticLogCoshMeanJet L ht
      have hd : ∀ z, HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
          (P.value z) z := hasDerivAt_fieldScalarLogCosh L ht
      refine ⟨J.transition P av.1 av.2 _ hv.1 hv.2 hd, ?_⟩
      change fieldSpinTransition av.1 av.2 _ J.value = _
      rw [hJ]
      rfl

theorem magneticLevelAtBias_has_bounded_jet (h : FieldStep) (i : Fin (h.depth + 1)) :
    ∃ J : MagneticContinuationJet, J.value = fun b => magneticLevelAtBias h b i := by
  have hL := scalarFieldIncrements_positive h
  obtain ⟨J, hJ⟩ := fieldScalarSquares_has_bounded_jet (scalarFieldIncrements h) hL
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet (scalarFieldIncrements h) hL
  have hd : ∀ z, HasDerivAt (fieldScalarValue (scalarFieldIncrements h)
      (fun y => Real.log (Real.cosh y))) (P.value z) z :=
    hasDerivAt_fieldScalarLogCosh _ hL
  refine ⟨J.transition P 0 (NNReal.mk (h.height 0) (h.nonneg 0)) _ hv.1 hv.2 hd, ?_⟩
  change fieldSpinTransition 0 _ _ J.value = _
  rw [hJ]
  rfl

end InvariantIsing

end

end OAI
