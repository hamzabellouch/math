import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsHistory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalarPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkTransport
open Construction Construction.CanonicalOccurrenceTransport HistorySymbolicEncoding
open CompensationEqualityPatterns

theorem internalLevel_le (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    CanonicalOccurrenceTransport.internalLevel seed i ≤ l := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    rcases i with i | i | i
    · exact le_rfl
    · exact (ih i).trans (Nat.le_succ l)
    · exact (ih i).trans (Nat.le_succ l)

@[simp] theorem internalLevel_ne_root (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    CanonicalOccurrenceTransport.internalLevel seed i ≠ l+1 := by
  have := internalLevel_le seed i
  omega

@[simp] theorem root_ne_internalLevel (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    l+1 ≠ CanonicalOccurrenceTransport.internalLevel seed i := (internalLevel_ne_root seed i).symm

def internalPairSample (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) :
    Internal seed l ⊕ Internal seed l → ℤ :=
  Sum.elim (fun i => coordinateSample seed h hh (.inr (.inr i)))
    (fun i => coordinateSample seed k hk (.inr (.inr i)))

theorem rootSample_injective (seed : List SourceSlot) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hh : TreeSourceLabels seed h) :
    Function.Injective (fun i : Fin (Template.current seed l).length =>
      coordinateSample seed h hh (.inr (.inl i))) := by
  intro i j he
  apply (finCongr (Template.matches_length (root_matches hh)).symm).injective
  apply HistoryPairBulkCoordinates.root_value_injective h hs
  simp only [coordinateSample, Function.comp_apply, coordinateEquiv,
    Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, HistoryOccurrenceVariables.integerSample] at he
  exact_mod_cast he

theorem samePairPattern_of_root_permutation (seed : List SourceSlot) {l : ℕ}
    {V W : ℕ → ℕ} {outside : List ℕ} (h k h' k' : History l)
    (hs : h.Supported V outside) (hs' : h'.Supported W outside)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i, coordinateSample seed k hk (.inr (.inl i)) =
      coordinateSample seed h hh (.inr (.inl (σ i))))
    (hroot' : ∀ i, coordinateSample seed k' hk' (.inr (.inl i)) =
      coordinateSample seed h' hh' (.inr (.inl (σ i))))
    (hint : ∀ i j : Internal seed l ⊕ Internal seed l,
      (pairedHistoryType seed l i = pairedHistoryType seed l j ∧
        internalPairSample seed h k hh hk i = internalPairSample seed h k hh hk j) ↔
      (pairedHistoryType seed l i = pairedHistoryType seed l j ∧
        internalPairSample seed h' k' hh' hk' i = internalPairSample seed h' k' hh' hk' j)) :
    SamePairPattern seed h k h' k' hh hk hh' hk' := by
  have hleft := rootSample_injective seed h hs hh
  have hleft' := rootSample_injective seed h' hs' hh'
  intro i j
  rcases i with (i | i | i) | (i | i | i) <;>
    rcases j with (j | j | j) | (j | j | j) <;>
    simp only [pairCoordinatePattern, Sum.elim_inl, Sum.elim_inr,
      coordinatePattern, coordinateLevel, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq, hroot, hroot',
      hleft.eq_iff, hleft'.eq_iff, true_and,
      internalLevel_ne_root, root_ne_internalLevel, false_and, iff_self]
  · exact hint (.inl i) (.inl j)
  · exact hint (.inl i) (.inr j)
  · exact hint (.inr i) (.inl j)
  · exact hint (.inr i) (.inr j)

end Ostmann.Arithmetic.HistoryPairBulkTransport

end

end OAI
