import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairRepresentativeVariables HistoryPairBulkCoordinates
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns
open Construction.CanonicalOccurrenceTransport HistorySymbolicEncoding
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

def blockSourceEquiv {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) {β : Type*} (e : Representative h k ≃ β) :
    (Bool ⊕ (Fin h.root.small.length ⊕ β)) ≃ PairKey h k :=
  (Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (Equiv.refl _) e.symm)).trans (sourceEquiv h k hs hperm)

@[simp] theorem blockSourceEquiv_giant {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) {β : Type*} (e : Representative h k ≃ β) (b : Bool) :
    blockSourceEquiv h k hs hperm e (.inl b) = leftMap h k (.inl b) := rfl

@[simp] theorem blockSourceEquiv_root {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) {β : Type*} (e : Representative h k ≃ β)
    (i : Fin h.root.small.length) :
    blockSourceEquiv h k hs hperm e (.inr (.inl i)) = rootKey h k i := rfl

@[simp] theorem blockSourceEquiv_block {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) {β : Type*} (e : Representative h k ≃ β) (q : β) :
    blockSourceEquiv h k hs hperm e (.inr (.inr q)) = representativeMap h k (e.symm q) := rfl

section Decoded
variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
  (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
  (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)
  {outside : List ℕ}
  (hs : (blockLeftHistory sources seed V l p b hvalid a f).Supported V outside)
  (hperm : a.small.Perm a'.small)

def decodedSourceEquiv :
    (Bool ⊕ (Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length ⊕ Block p)) ≃
      PairKey (blockLeftHistory sources seed V l p b hvalid a f)
        (blockRightHistory sources seed V l p b hvalid a' g) :=
  blockSourceEquiv _ _ hs
    (by simpa only [blockLeftHistory,blockRightHistory,decodeHistory_root] using hperm)
    (decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha')

@[simp] theorem decodedSourceEquiv_block_sample (q : Block p) :
    pairSample _ _ (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
      (.inr (.inr q))) = ((b.val q).val : ℤ) := by
  change (prime _ _ ((decodedRepresentativeBlockEquiv
    sources seed V l p b hvalid a a' f g ha ha').symm q) : ℤ) = _
  rw [decodedRepresentativeBlockEquiv_prime sources seed V l p b hvalid a a' f g ha ha',
    Equiv.apply_symm_apply]

@[simp] theorem decodedSourceEquiv_root_sample
    (i : Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length) :
    pairSample _ _ (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
      (.inr (.inl i))) =
        ((blockLeftHistory sources seed V l p b hvalid a f).root.small.get i).value := rfl

@[simp] theorem decodedSourceEquiv_giant_sample (t : Bool) :
    pairSample _ _ (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
      (.inl t)) = (if t then (a.giantMinus : ℤ) else (a.giantPlus : ℤ)) := by
  cases t
  · change ((blockLeftHistory sources seed V l p b hvalid a f).root.giantPlus : ℤ) = _
    simp only [blockLeftHistory,decodeHistory_root, Bool.false_eq_true, ↓reduceIte]
  · change ((blockLeftHistory sources seed V l p b hvalid a f).root.giantMinus : ℤ) = _
    simp only [blockLeftHistory,decodeHistory_root, ↓reduceIte]

theorem decodedSourceEquiv_sample
    (i : Bool ⊕ (Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length ⊕ Block p)) :
    pairSample _ _ (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm i) =
      Sum.elim (fun t => if t then (a.giantMinus : ℤ) else (a.giantPlus : ℤ))
        (Sum.elim (fun j => (((blockLeftHistory sources seed V l p b hvalid a f).root.small.get j).value : ℤ))
          (fun q => ((b.val q).val : ℤ))) i := by
  rcases i with t | j | q
  · exact decodedSourceEquiv_giant_sample sources seed V l p b hvalid a a' f g ha ha' hs hperm t
  · exact decodedSourceEquiv_root_sample sources seed V l p b hvalid a a' f g ha ha' hs hperm j
  · exact decodedSourceEquiv_block_sample sources seed V l p b hvalid a a' f g ha ha' hs hperm q

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceCoordinates

end

end OAI
