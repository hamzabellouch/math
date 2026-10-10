import OAI.Probability.InvariantIsing.Fields.FieldAffineScalarBridge
import OAI.Probability.InvariantIsing.Fields.FieldScalarSquareOrder

namespace OAI

/-! Evenness, monotonicity and the unit spin bound for the actual affine
log-cosh recursion. These hypotheses of the mixed-order argument are
discharged from the explicit terminal function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

theorem fieldAffineFamily_shape (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t)
    (hζ : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    Function.Even (fun z => (fieldAffineFamily I hI L hL).U (t, z)) ∧
    Function.Odd (fun z => (fieldAffineFamily I hI L hL).X (t, z)) ∧
    MonotoneOn (fun z => (fieldAffineFamily I hI L hL).X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ (fieldAffineFamily I hI L hL).X (t, z)) ∧
    (∀ z, |(fieldAffineFamily I hI L hL).X (t, z)| ≤ 1) := by
  have hi : ∀ av ∈ fieldAffineIncrements L t, 0 < av.1 := by
    intro av hav
    obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
    exact hζ bv hb
  have hF : Measurable (fun z : ℝ => Real.log (Real.cosh z)) := by fun_prop
  have hFg : HasLinearGrowth (fun z : ℝ => Real.log (Real.cosh z)) :=
    (fieldLogCoshFamily I).growth 0
  have hFe : Function.Even (fun z : ℝ => Real.log (Real.cosh z)) := by
    intro z
    simp only [Real.cosh_neg]
  have ha : Measurable (fun z : ℝ => Real.tanh z) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hao : Function.Odd Real.tanh := Real.tanh_neg
  have ham : MonotoneOn Real.tanh (Ici 0) := field_tanh_monotone.monotoneOn _
  have hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ Real.tanh z := fun _ hz => field_tanh_nonneg hz
  have hv := fieldScalarValue_even (fieldAffineIncrements L t) hi hF hFg hFe
  have hm := fieldScalarMean_shape (fieldAffineIncrements L t) hi hF hFg hFe
    ha hao ham hap field_abs_tanh_le_one
  have hb := (fieldScalarMean_regular (fieldAffineIncrements L t) hi hF hFg
    ha field_abs_tanh_le_one).2
  have hU : (fun z => (fieldAffineFamily I hI L hL).U (t, z)) =
      fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
    rw [fieldAffineFamily_value I hI L hL]
    exact fieldAffineValue_scalar L t
  have hX := fieldAffineFamily_mean I hI L hL t
  have hXp (z : ℝ) := congrFun hX z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    exact hv
  · rw [hX]
    exact hm.1
  · rw [hX]
    exact hm.2.1
  · intro z hz
    rw [hXp]
    exact hm.2.2 z hz
  · intro z
    rw [hXp]
    exact hb z

end InvariantIsing

end

end OAI
