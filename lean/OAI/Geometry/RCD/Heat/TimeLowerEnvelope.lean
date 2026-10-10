import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! # A bounded monotone envelope of prescribed time slices

The baseline makes the supremum nonempty at every real time, including
times before the first prescribed slice.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def timeLowerEnvelope (M : ℝ) (s v : ℕ → ℝ) (t : ℝ) : ℝ :=
  sSup ({-M} ∪ {y | ∃ i, s i < t ∧ y = v i})

private theorem envelope_nonempty (M : ℝ) (s v : ℕ → ℝ) (t : ℝ) :
    ({-M} ∪ {y | ∃ i, s i < t ∧ y = v i}).Nonempty :=
  ⟨-M,Or.inl (mem_singleton _)⟩

private theorem envelope_bddAbove {M : ℝ} (hM : 0 ≤ M) (s v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ M) (t : ℝ) :
    BddAbove ({-M} ∪ {y | ∃ i, s i < t ∧ y = v i}) := by
  refine ⟨M,?_⟩
  rintro y (hy | ⟨i,_hi,rfl⟩)
  · simpa only [mem_singleton_iff.mp hy] using neg_le_self hM
  · exact (abs_le.mp (hv i)).2

theorem timeLowerEnvelope_bounds {M : ℝ} (hM : 0 ≤ M) (s v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ M) (t : ℝ) : |timeLowerEnvelope M s v t| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact le_csSup (envelope_bddAbove hM s v hv t) (Or.inl (mem_singleton _))
  · apply csSup_le (envelope_nonempty M s v t)
    rintro y (hy | ⟨i,_hi,rfl⟩)
    · simpa only [mem_singleton_iff.mp hy] using neg_le_self hM
    · exact (abs_le.mp (hv i)).2

theorem timeLowerEnvelope_monotone {M : ℝ} (hM : 0 ≤ M) (s v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ M) : Monotone (timeLowerEnvelope M s v) := by
  intro t u htu
  apply csSup_le_csSup (envelope_bddAbove hM s v hv u) (envelope_nonempty M s v t)
  rintro y (hy | ⟨i,hi,rfl⟩)
  · exact Or.inl hy
  · exact Or.inr ⟨i,hi.trans_le htu,rfl⟩

theorem sample_le_timeLowerEnvelope {M : ℝ} (hM : 0 ≤ M) (s v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ M) {i : ℕ} {t : ℝ} (hi : s i < t) :
    v i ≤ timeLowerEnvelope M s v t :=
  le_csSup (envelope_bddAbove hM s v hv t) (Or.inr ⟨i,hi,rfl⟩)

theorem timeLowerEnvelope_le_sample {M : ℝ} (s v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ M) (horder : ∀ i j, s i ≤ s j → v i ≤ v j)
    {i : ℕ} {t : ℝ} (hi : t ≤ s i) : timeLowerEnvelope M s v t ≤ v i := by
  apply csSup_le (envelope_nonempty M s v t)
  rintro y (hy | ⟨j,hj,rfl⟩)
  · simpa only [mem_singleton_iff.mp hy] using (abs_le.mp (hv i)).1
  · exact horder j i (hj.le.trans hi)

theorem timeLowerEnvelope_countable_discontinuities {M : ℝ} (hM : 0 ≤ M)
    (s v : ℕ → ℝ) (hv : ∀ i, |v i| ≤ M) :
    Set.Countable {t | ¬ContinuousAt (timeLowerEnvelope M s v) t} :=
  (timeLowerEnvelope_monotone hM s v hv).countable_not_continuousAt

end RegularPointCoordinates

end

end OAI
