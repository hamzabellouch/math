import OAI.Probability.InvariantIsing.Magnetic.MagneticFourJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarContinuation

namespace OAI

/-! Every actual finite scalar Ising mean, and every continued square
observable, has the fourth spatial derivative required in the parabolic
comparison. No additional smoothness hypothesis is imposed on the model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

private def logCoshMeanFourJet : MagneticContinuationFourJet where
  toMagneticContinuationJet := magneticLogCoshMeanJet [] (by simp)
  fourth := fun z => 16 * Real.tanh z * (1 / Real.cosh z ^ 2) ^ 2 -
    8 * Real.tanh z ^ 3 * (1 / Real.cosh z ^ 2)
  mFourth := by
    simp only [Real.tanh_eq]
    fun_prop
  bFourth := by
    let P := magneticLogCoshMeanJet [] (by simp)
    have hM := P.bValue
    have hQ := P.bFirst
    change MagneticContinuationBound Real.tanh at hM
    change MagneticContinuationBound (fun z => 1 / Real.cosh z ^ 2) at hQ
    have hM3 : MagneticContinuationBound (fun z => Real.tanh z ^ 3) := by
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using (hM.mul hM).mul hM
    have hQ2 : MagneticContinuationBound (fun z => (1 / Real.cosh z ^ 2) ^ 2) := by
      simpa only [pow_two] using hQ.mul hQ
    exact (((MagneticContinuationBound.const 16).mul hM).mul hQ2).sub
      (((MagneticContinuationBound.const 8).mul hM3).mul hQ)
  dThird := fun z => by
    change HasDerivAt fieldLogCoshFourth _ z
    have hM := field_hasDerivAt_tanh z
    have hQ := field_logCosh_third_derivative z
    have hd := ((hQ.pow 2).const_mul (-2)).add (((hM.pow 2).const_mul 4).mul hQ)
    convert hd using 1
    · rfl
    · simp only [div_eq_mul_inv, Pi.pow_apply]
      ring

lemma fieldScalarMean_has_bounded_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    ∃ J : MagneticContinuationFourJet,
      J.value = fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => exact ⟨logCoshMeanFourJet, rfl⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    obtain ⟨J, hJ⟩ := ih ht
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hd : ∀ z, HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
        (J.value z) z := by
      rw [hJ]
      exact hasDerivAt_fieldScalarLogCosh L ht
    refine ⟨J.transition J.toMagneticContinuationJet av.1 av.2 _ hv.1 hv.2 hd, ?_⟩
    change fieldSpinTransition av.1 av.2 _ J.value = _
    rw [hJ]
    rfl

def magneticLogCoshMeanFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : MagneticContinuationFourJet :=
  (fieldScalarMean_has_bounded_fourJet L hL).choose

lemma magneticLogCoshMeanFourJet_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    (magneticLogCoshMeanFourJet L hL).toMagneticContinuationJet = magneticLogCoshMeanJet L hL := by
  apply MagneticContinuationJet.eq_of_value_eq
  exact (fieldScalarMean_has_bounded_fourJet L hL).choose_spec

lemma fieldScalarSquares_has_bounded_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    ∃ J : MagneticContinuationFourJet,
      J.value = fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i := by
  induction L with
  | nil =>
    refine ⟨logCoshMeanFourJet.square, ?_⟩
    rfl
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨(magneticLogCoshMeanFourJet (av :: L) hL).square, ?_⟩
      change (fun z => ((magneticLogCoshMeanFourJet (av :: L) hL).value z) ^ 2) = _
      have he := congrArg MagneticContinuationJet.value (magneticLogCoshMeanFourJet_eq (av :: L) hL)
      rw [he]
      rfl
    · obtain ⟨J, hJ⟩ := ih ht j
      have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      let P := magneticLogCoshMeanJet L ht
      have hd : ∀ z, HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
          (P.value z) z := hasDerivAt_fieldScalarLogCosh L ht
      refine ⟨J.transition P av.1 av.2 _ hv.1 hv.2 hd, ?_⟩
      change fieldSpinTransition av.1 av.2 _ J.value = _
      rw [hJ]
      rfl

end InvariantIsing

end

end OAI
