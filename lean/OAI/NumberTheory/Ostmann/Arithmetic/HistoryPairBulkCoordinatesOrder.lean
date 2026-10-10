import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistoryPairPattern
open HistoryActiveCoordinates HistoryPairGiantCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def matchedRootPosition {T : List SourceSlot} {h : History l}
    (hh : Template.Matches T h.root.small) : Fin T.length ≃ Fin h.root.small.length :=
  finCongr (Template.matches_length hh).symm

@[simp] theorem matchedRootPosition_role {T : List SourceSlot} {h : History l}
    (hh : Template.Matches T h.root.small) (i : Fin T.length) :
    (h.root.small.get (matchedRootPosition hh i)).role = T[i].role :=
  congrArg SourceSlot.role (matches_get_source hh i)

def matchedBulkPositions {T : List SourceSlot} {h : History l}
    (hh : Template.Matches T h.root.small) : Conclusion.BulkPosition T ≃ RootBulkPosition h :=
  (matchedRootPosition hh).subtypeEquiv (fun i => by
    change T[i].role = .bulk ↔ (h.root.small.get (matchedRootPosition hh i)).role = .bulk
    rw [matchedRootPosition_role])

def orderedEquiv (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small) :
    (Fin (2^l) × Fin m) ≃ bulkCoordinates h k :=
  ((Conclusion.currentBulkPositionEquiv m k₀ l).symm.trans (matchedBulkPositions hh)).trans
    (bulkEquiv h k hs)

def orderedKey (m k₀ : ℕ) (h k : History l)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (u : Fin (2^l) × Fin m) : PairKey h k :=
  rootKey h k (matchedRootPosition hh ((Conclusion.currentBulkPositionEquiv m k₀ l).symm u).val)

@[simp] theorem orderedEquiv_val (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (u : Fin (2^l) × Fin m) : (orderedEquiv m k₀ h k hs hh u).val = orderedKey m k₀ h k hh u := rfl

theorem orderedKey_injective (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small) :
    Function.Injective (orderedKey m k₀ h k hh) := by
  intro i j he
  exact (orderedEquiv m k₀ h k hs hh).injective (Subtype.ext he)

def insertOrdered (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (x : Fin (2^l) × Fin m → ℝ) : PairKey h k → ℝ :=
  HistoryActiveCoordinates.insert (bulkCoordinates h k) (pairBackground h k)
    (fun i => x ((orderedEquiv m k₀ h k hs hh).symm i))

@[simp] theorem insertOrdered_left (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (x : Fin (2^l) × Fin m → ℝ) (u : Fin (2^l) × Fin m) :
    insertOrdered m k₀ h k hs hh x (orderedKey m k₀ h k hh u) = x u := by
  change HistoryActiveCoordinates.insert _ _ _ (orderedEquiv m k₀ h k hs hh u).val = _
  rw [HistoryActiveCoordinates.insert, dite_eq_left (orderedEquiv m k₀ h k hs hh u).property]
  change x ((orderedEquiv m k₀ h k hs hh).symm (orderedEquiv m k₀ h k hs hh u)) = x u
  rw [Equiv.symm_apply_apply]

theorem matchedRootPosition_value {sources : SourceFamily} {T : List SourceSlot}
    {h : History l} (hh : Template.Matches T h.root.small) (x : SourceAssignment sources T)
    (hx : h.root.small = assignedSlots sources T x) (i : Fin T.length) :
    (h.root.small.get (matchedRootPosition hh i)).value = (x i : ℕ) := by
  have hi : i.val < h.root.small.length := by
    simpa only [Template.matches_length hh] using i.isLt
  change (h.root.small[i.val]).value = (x i : ℕ)
  simp only [hx, assignedSlots, Template.sample, List.getElem_ofFn]

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
