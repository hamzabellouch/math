import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryRepeatedRenaming HistoryActiveCoordinates HistorySymbolicEncoding
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

structure RootMatching (h k : History l) where
  positions : Fin k.root.small.length ≃ Fin h.root.small.length
  value : ∀ i, (k.root.small.get i).value = (h.root.small.get (positions i)).value
  bulk : ∀ i, (k.root.small.get i).role = .bulk ↔
    (h.root.small.get (positions i)).role = .bulk

theorem RootMatching.key_eq {h k : History l} (e : RootMatching h k)
    (i : Fin k.root.small.length) :
    rightMap h k (.inr (.inl i)) = rootKey h k (e.positions i) := by
  apply Subtype.ext
  change Sum.inr (l+1, ((k.root.small.get i).value : ℤ)) =
    Sum.inr (l+1, ((h.root.small.get (e.positions i)).value : ℤ))
  rw [e.value]

theorem right_nonbulk_not_mem (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (i : Fin k.root.small.length)
    (hi : (k.root.small.get i).role ≠ .bulk) :
    rightMap h k (.inr (.inl i)) ∉ bulkCoordinates h k := by
  rw [e.key_eq]
  exact left_nonbulk_not_mem h k hs _ (fun hq => hi ((e.bulk i).mpr hq))

def insertBulk (h k : History l) (hs : h.Supported V outside)
    (x : RootBulkPosition h → ℝ) : PairKey h k → ℝ :=
  HistoryActiveCoordinates.insert (bulkCoordinates h k) (pairBackground h k)
    (fun i => x ((bulkEquiv h k hs).symm i))

@[simp] theorem insertBulk_left (h k : History l) (hs : h.Supported V outside)
    (x : RootBulkPosition h → ℝ) (i : RootBulkPosition h) :
    insertBulk h k hs x (rootKey h k i.val) = x i := by
  change HistoryActiveCoordinates.insert _ _ _ (bulkEquiv h k hs i).val = _
  rw [HistoryActiveCoordinates.insert, dite_eq_left (bulkEquiv h k hs i).property]
  change x ((bulkEquiv h k hs).symm (bulkEquiv h k hs i)) = x i
  rw [Equiv.symm_apply_apply]

@[simp] theorem insertBulk_right (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (x : RootBulkPosition h → ℝ) (i : RootBulkPosition k) :
    insertBulk h k hs x (rightMap h k (.inr (.inl i.val))) =
      x ⟨e.positions i.val, (e.bulk i.val).mp i.property⟩ := by
  rw [e.key_eq]
  exact insertBulk_left h k hs x ⟨_, (e.bulk i.val).mp i.property⟩

theorem insertBulk_frozen (h k : History l) (hs : h.Supported V outside)
    (x : RootBulkPosition h → ℝ) (i : PairKey h k) (hi : i ∉ bulkCoordinates h k) :
    insertBulk h k hs x i = pairBackground h k i := by
  simp only [insertBulk, HistoryActiveCoordinates.insert, dite_eq_right hi]

theorem sourceBounds {b k₀ : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h k : History l) (hs : h.Supported V outside) (e : RootMatching h k)
    (hh : SourceDomain b k₀ G center h (fun i => (integerSample h i : ℝ)))
    (hk : SourceDomain b k₀ G center k (fun i => (integerSample k i : ℝ)))
    (lo hi : bulkCoordinates h k → ℝ) :
    SourceBounds b k₀ G center h (leftMap h k) (bulkCoordinates h k) (pairBackground h k) lo hi ∧
    SourceBounds b k₀ G center k (rightMap h k) (bulkCoordinates h k) (pairBackground h k) lo hi := by
  constructor
  · refine ⟨HistoryGiantSourceBounds.left_background_sourceDomain h k hh, ?_, ?_⟩
    · intro i q hiq hq hm
      rcases i with a | i | i
      · cases hiq
      · have he : h.root.small.get i = q := Option.some.inj hiq
        exact (left_nonbulk_not_mem h k hs i (he ▸ hq) hm).elim
      · exact (left_internal_not_mem h k i hm).elim
    · intro a hm
      exact (left_giant_not_mem h k a hm).elim
  · refine ⟨HistoryGiantSourceBounds.right_background_sourceDomain h k hh hk, ?_, ?_⟩
    · intro i q hiq hq hm
      rcases i with a | i | i
      · cases hiq
      · have he : k.root.small.get i = q := Option.some.inj hiq
        exact (right_nonbulk_not_mem h k hs e i (he ▸ hq) hm).elim
      · exact (right_internal_not_mem h k i hm).elim
    · intro a hm
      exact (right_giant_not_mem h k a hm).elim

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
