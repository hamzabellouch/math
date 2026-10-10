import OAI.NumberTheory.TwoPoint.Walks.WordResampling

namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

/-- A segment inherits the original labels, including shared prime classes. -/
def segment (w : LabeledPrimeWord ι) (a n : ℕ) : LabeledPrimeWord ι where
  word := (w.word.drop a).take n
  labels i := w.labels ⟨a + i.val, by
    have hi : i.val < min n (w.word.length - a) := by
      simpa only [List.length_take, List.length_drop] using i.isLt
    have := (lt_min_iff.mp hi).2
    omega⟩

omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]

omit [DecidableEq ι] in
lemma segment_resample_word (w : LabeledPrimeWord ι) (a n : ℕ) (value : ι → ℕ) :
    ((w.segment a n).resample value).word = ((w.resample value).word.drop a).take n := by
  apply List.ext_getElem
  · simp only [resample_length, segment_length, List.length_take, List.length_drop]
  · intro i hi hj
    have hi' : i < ((w.word.drop a).take n).length := by
      simpa only [resample_length, segment] using hi
    have hj' : a + i < w.word.length := by
      have ht : i < min n (w.word.length - a) := by
        simpa only [List.length_take, List.length_drop] using hi'
      have := (lt_min_iff.mp ht).2
      omega
    rw [List.getElem_take, List.getElem_drop]
    simp only [resample, List.getElem_ofFn]
    change (⟨(((w.word.drop a).take n)[i]'hi').forward,
      ∏ z ∈ w.labels ⟨a + i, hj'⟩, value z,
      (((w.word.drop a).take n)[i]'hi').padding⟩ : SignedStep) =
      ⟨(w.word[a + i]'hj').forward, ∏ z ∈ w.labels ⟨a + i, hj'⟩, value z,
        (w.word[a + i]'hj').padding⟩
    simp only [List.getElem_take, List.getElem_drop]

omit [DecidableEq ι] in
lemma segment_realizes (w : LabeledPrimeWord ι) (a n : ℕ) (value : ι → ℕ)
    (hw : w.Realizes value) : (w.segment a n).Realizes value := by
  intro i
  simp only [segment, List.getElem_take, List.getElem_drop]
  exact hw ⟨a + i.val, by
    have hi : i.val < min n (w.word.length - a) := by
      simpa only [segment_length] using i.isLt
    have := (lt_min_iff.mp hi).2
    omega⟩

end LabeledPrimeWord
end TwoPointCorrelations

end OAI
