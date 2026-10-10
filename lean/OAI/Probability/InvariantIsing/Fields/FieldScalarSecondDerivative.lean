import OAI.Probability.InvariantIsing.Fields.FieldSpinSecondDerivative
import OAI.Probability.InvariantIsing.Fields.FieldScalarDerivative

namespace OAI

/-! Bounded second derivatives through the actual finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarSecond : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, b => b
  | av :: L, F, a, b => fun z =>
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSecond L F a b) z +
        av.1 * (fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fun u => (fieldScalarMean L F a u) ^ 2) z -
            (fieldScalarMean (av :: L) F a z) ^ 2)

def fieldScalarSecondCap (L : List (ℝ × ℝ≥0)) (K C : ℝ) : ℝ :=
  L.foldr (fun av c => c + 2 * |av.1| * K ^ 2) C

theorem fieldScalarSecond_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {K C : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ C) :
    Measurable (fieldScalarSecond L F a b) ∧
      ∀ z, |fieldScalarSecond L F a b z| ≤ fieldScalarSecondCap L K C := by
  induction L with
  | nil => exact ⟨hb, hbB⟩
  | cons av L ih =>
    have htail (bv) (h : bv ∈ L) := hL bv (List.mem_cons_of_mem av h)
    obtain ⟨hm, hB⟩ := ih htail
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hnew := fieldScalarMean_regular (av :: L) hL hF hG ha haB
    refine ⟨?_, ?_⟩
    · exact (measurable_fieldSpinTransition av.1 av.2 hval.1 hm).add
        (((measurable_fieldSpinTransition av.1 av.2 hval.1 (hmean.1.pow_const 2)).sub
          (hnew.1.pow_const 2)).const_mul av.1)
    · intro z
      have h := fieldSpinTransition_derivative_bound av.1 av.2 hval.1 hval.2
        hK hK hmean.2 hmean.2 hB z
      simpa only [fieldScalarSecond, fieldScalarSecondCap, List.foldr_cons,
        fieldScalarMean, pow_two, mul_assoc] using h

theorem hasDerivAt_fieldScalarMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {K C : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ C)
    (hd : ∀ z, HasDerivAt F (a z) z) (hdd : ∀ z, HasDerivAt a (b z) z) (z : ℝ) :
    HasDerivAt (fieldScalarMean L F a) (fieldScalarSecond L F a b z) z := by
  induction L generalizing z with
  | nil => exact hdd z
  | cons av L ih =>
    have htail (bv) (h : bv ∈ L) := hL bv (List.mem_cons_of_mem av h)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hsecond := fieldScalarSecond_regular L htail hF hG ha hb hK haB hbB
    have h := hasDerivAt_fieldSpinTransition av.1 av.2 hval.1 hval.2 hmean.1 hmean.1
      hsecond.1 hK hK hmean.2 hmean.2 hsecond.2
      (hasDerivAt_fieldScalarValue L htail hF hG ha hK haB hd) (ih htail) z
    simpa only [fieldScalarMean, fieldScalarSecond, pow_two] using h

end InvariantIsing

end

end OAI
