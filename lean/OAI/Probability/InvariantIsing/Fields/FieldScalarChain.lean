import OAI.Probability.InvariantIsing.Fields.FieldSpinTransition
import OAI.Probability.InvariantIsing.Fields.FieldRadialBackward

namespace OAI

/-! Actual one-dimensional backward values, physical conditional spin
means, and conditional second moments for a finite list of field increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldScalarValue (L : List (ℝ × ℝ≥0)) (F : ℝ → ℝ) : ℝ → ℝ :=
  L.foldr (fun av f => gaussianOperator av.1 av.2 f) F

def fieldScalarMean : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | [], _, a => a
  | av :: L, F, a => fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarMean L F a)

lemma fieldScalarValue_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) :
    Measurable (fieldScalarValue L F) ∧ HasLinearGrowth (fieldScalarValue L F) := by
  induction L with
  | nil => exact ⟨hF, hG⟩
  | cons av L ih =>
    have ht := ih (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
    exact gaussianOperator_positive_growth ht.1 ht.2 (hL av (List.mem_cons_self)) av.2

lemma fieldScalarMean_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) {B : ℝ} (haB : ∀ u, |a u| ≤ B) :
    Measurable (fieldScalarMean L F a) ∧ ∀ z, |fieldScalarMean L F a z| ≤ B := by
  induction L with
  | nil => exact ⟨ha, haB⟩
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := ih htail
    exact ⟨measurable_fieldSpinTransition av.1 av.2 hval.1 hmean.1,
      fieldSpinTransition_bound av.1 av.2 hval.1 hval.2 hmean.2⟩

/-- The entry indexed by `i` is the conditional expectation of the square
of the physical spin mean at level `i`, given the starting position. -/
def fieldScalarSquares : (L : List (ℝ × ℝ≥0)) → (ℝ → ℝ) → (ℝ → ℝ) →
    Fin (L.length + 1) → ℝ → ℝ
  | [], _, a => fun _ z => (a z) ^ 2
  | av :: L, F, a => Fin.cons (fun z => (fieldScalarMean (av :: L) F a z) ^ 2)
      (fun i => fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a i))

@[simp] lemma fieldScalarSquares_zero (L : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) (z : ℝ) :
    fieldScalarSquares L F a 0 z = (fieldScalarMean L F a z) ^ 2 := by
  cases L <;> rfl

lemma fieldScalarSquares_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) :
    ∀ i, Measurable (fieldScalarSquares L F a i) ∧
      ∀ z, fieldScalarSquares L F a i z ∈ Icc (0 : ℝ) 1 := by
  induction L with
  | nil =>
    intro i
    refine ⟨ha.pow_const 2, fun z => ⟨sq_nonneg _, ?_⟩⟩
    have hab := abs_le.mp (haB z)
    change (a z) ^ 2 ≤ 1
    nlinarith
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular (av :: L) hL hF hG ha haB
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨hmean.1.pow_const 2, fun z => ⟨sq_nonneg _, ?_⟩⟩
      have hab := abs_le.mp (hmean.2 z)
      change (fieldScalarMean (av :: L) F a z) ^ 2 ≤ 1
      nlinarith
    · have hj := ih htail j
      refine ⟨measurable_fieldSpinTransition av.1 av.2 hval.1 hj.1, fun z => ⟨?_, ?_⟩⟩
      · exact integral_nonneg (fun u => (hj.2 u).1)
      · have hb : ∀ u, |fieldScalarSquares L F a j u| ≤ 1 := by
          intro u
          rw [abs_of_nonneg (hj.2 u).1]
          exact (hj.2 u).2
        exact (le_abs_self _).trans (fieldSpinTransition_bound av.1 av.2 hval.1 hval.2 hb z)

end InvariantIsing

end

end OAI
