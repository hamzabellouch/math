import OAI.NumberTheory.TwoPoint.Bounds.RelationReindex
import OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding

namespace OAI

/-! Numerical resampling preserves the symbolic witness relations. -/

namespace TwoPointCorrelations

open Finset

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

/-- Equality of the symbolic data, with an explicit position-preserving index map. -/
structure PatternEquiv (w v : LabeledPrimeWord ι) where
  index : Fin w.word.length ≃ Fin v.word.length
  index_val : ∀ i, (index i).val = i.val
  monomial : ∀ h i, v.monomial h (index i) = w.monomial h i

omit [DecidableEq ι] in
lemma PatternEquiv.interval {w v : LabeledPrimeWord ι} (e : PatternEquiv w v)
    (h a b : ℕ) (i : Fin w.word.length) :
    v.intervalRelation h a b (e.index i) = w.intervalRelation h a b i := by
  simp only [intervalRelation, e.index_val, e.monomial]

/-- Only the numerical tuple products change. Orientations, padding, and labels remain fixed. -/
def resample (w : LabeledPrimeWord ι) (value : ι → ℕ) : LabeledPrimeWord ι where
  word := List.ofFn (fun i : Fin w.word.length =>
    ⟨(w.word[i.val]'i.isLt).forward, ∏ z ∈ w.labels i, value z,
      (w.word[i.val]'i.isLt).padding⟩)
  labels i := w.labels ⟨i.val, by simpa using i.isLt⟩

omit [DecidableEq ι] in
@[simp] lemma resample_length (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    (w.resample value).word.length = w.word.length := by
  simp [resample]

omit [DecidableEq ι] in
lemma resample_realizes (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    (w.resample value).Realizes value := by
  intro i
  simp [resample, List.getElem_ofFn]

def resamplePattern (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    PatternEquiv w (w.resample value) where
  index := finCongr (w.resample_length value).symm
  index_val _ := rfl
  monomial h i := by
    simp only [monomial, resample, List.getElem_ofFn]
    rfl

end LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

def comparisonIndexEquiv {main wi wj main' wi' wj' : LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hi : LabeledPrimeWord.PatternEquiv wi wi')
    (hj : LabeledPrimeWord.PatternEquiv wj wj') :
    (Fin main.word.length ⊕ (Fin wi.word.length ⊕ Fin wj.word.length)) ≃
      (Fin main'.word.length ⊕ (Fin wi'.word.length ⊕ Fin wj'.word.length)) :=
  Equiv.sumCongr hm.index (Equiv.sumCongr hi.index hj.index)

lemma comparisonRelation_pattern {main wi wj main' wi' wj' : LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hi : LabeledPrimeWord.PatternEquiv wi wi')
    (hj : LabeledPrimeWord.PatternEquiv wj wj') (h a b r s : ℕ)
    (i : Fin main.word.length ⊕ (Fin wi.word.length ⊕ Fin wj.word.length)) :
    comparisonRelation main' wi' wj' h a b r s (comparisonIndexEquiv hm hi hj i) =
      comparisonRelation main wi wj h a b r s i := by
  rcases i with i | i | i
  · exact hm.interval h a b i
  · exact hi.interval h 0 r i
  · change PrimeMonomial.mk (-(wj'.intervalRelation h 0 s (hj.index i)).coefficient)
        (wj'.intervalRelation h 0 s (hj.index i)).labels = _
    rw [hj.interval h 0 s i]
    rfl

namespace WitnessSystemData

variable {n N : ℕ}

/-- Every mode decodes to the same expression after changing numerical tuples. -/
theorem relationPattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) (i : d.chosen) :
    (∃ e : (d.relation main word h i).Term ≃ (d.relation main' word' h i).Term,
      ∀ t, (d.relation main' word' h i).monomial (e t) = (d.relation main word h i).monomial t) := by
  rcases d with ⟨mode, chosen, slot⟩
  fin_cases mode
  · exact ⟨(hw i).index, fun t => (hw i).interval _ _ _ t⟩
  · exact ⟨(hw i).index, fun t => (hw i).interval _ _ _ t⟩
  · exact ⟨comparisonIndexEquiv hm (hw i) (hw (slot i).2.2.1),
      comparisonRelation_pattern hm (hw i) (hw (slot i).2.2.1) _ _ _ _ _⟩
  · exact ⟨comparisonIndexEquiv hm (hw (slot i).2.2.1) (hw i),
      comparisonRelation_pattern hm (hw (slot i).2.2.1) (hw i) _ _ _ _ _⟩

lemma holds_pattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) (x : ι → ℤ) :
    d.Holds main' word' h x ↔ d.Holds main word h x := by
  unfold Holds
  apply forall_congr'
  intro i
  obtain ⟨e, he⟩ := d.relationPattern hm hw h i
  exact primeRelationEvent_reindex e _ _ he _ _ _

lemma triangular_pattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) :
    d.Triangular main' word' h ↔ d.Triangular main word h := by
  have hs (i : d.chosen) : primeRelationSupport (d.relation main' word' h i).monomial =
      primeRelationSupport (d.relation main word h i).monomial := by
    obtain ⟨e, he⟩ := d.relationPattern hm hw h i
    exact primeRelationSupport_reindex e _ _ he
  simp only [Triangular, hs]

end WitnessSystemData

end TwoPointCorrelations

end OAI
