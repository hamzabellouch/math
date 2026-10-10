import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsKernels
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesPair
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesValues

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns
open Construction Construction.CanonicalOccurrenceTransport HistoryPairRows HistoryPairRepresentatives
open CompensationEqualityPatterns HistorySymbolicEncoding HistoryPairPolynomialKernel
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
  (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)

def blockSourceDraws : PairedInternalSourceDraws sources seed l :=
  fun i => ⟨(expand p b i).val, hvalid i⟩

def blockLeftChoices (f : FrequencyChoices V l) : HistoryChoices sources seed V l :=
  assembleHistoryChoices sources seed V l f (fun i => blockSourceDraws sources seed l p b hvalid (.inl i))

def blockRightChoices (g : FrequencyChoices V l) : HistoryChoices sources seed V l :=
  assembleHistoryChoices sources seed V l g (fun i => blockSourceDraws sources seed l p b hvalid (.inr i))

def blockLeftHistory (a : State) (f : FrequencyChoices V l) : History l :=
  decodeHistory sources seed V l a (blockLeftChoices sources seed V l p b hvalid f)

def blockRightHistory (a : State) (g : FrequencyChoices V l) : History l :=
  decodeHistory sources seed V l a (blockRightChoices sources seed V l p b hvalid g)

variable (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)

include ha in
theorem blockLeftLabels : TreeSourceLabels seed (blockLeftHistory sources seed V l p b hvalid a f) :=
  decoded_tree_source_labels sources seed V l a _ ha

include ha' in
theorem blockRightLabels : TreeSourceLabels seed (blockRightHistory sources seed V l p b hvalid a' g) :=
  decoded_tree_source_labels sources seed V l a' _ ha'

theorem decoded_pair_slot_eq (i : Internal seed l ⊕ Internal seed l) :
    (slot (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g)
      (pairedInternalEquiv seed _ _
        (blockLeftLabels sources seed V l p b hvalid a f ha)
        (blockRightLabels sources seed V l p b hvalid a' g ha') i)).value =
      expand p (natBlockDraw p b Subtype.val Subtype.val_injective) i := by
  cases i with
  | inl i =>
    have hv := decoded_internalSlot_eq_historyDraw sources seed V l a
      (blockLeftChoices sources seed V l p b hvalid f) ha i
    have hd := congrArg (fun x : InternalSourceDraws sources seed l => (x i).val)
      (historyDraws_assemble sources seed V l f
        (fun j => blockSourceDraws sources seed l p b hvalid (.inl j)))
    exact hv.trans hd
  | inr i =>
    have hv := decoded_internalSlot_eq_historyDraw sources seed V l a'
      (blockRightChoices sources seed V l p b hvalid g) ha' i
    have hd := congrArg (fun x : InternalSourceDraws sources seed l => (x i).val)
      (historyDraws_assemble sources seed V l g
        (fun j => blockSourceDraws sources seed l p b hvalid (.inr j)))
    exact hv.trans hd

def decodedRepresentativeBlockEquiv :
    Representative (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g) ≃ Block p :=
  representativeBlockEquiv seed _ _
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha') p
    (natBlockDraw p b Subtype.val Subtype.val_injective)
    (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha')

theorem decodedRepresentativeBlockEquiv_prime
    (r : Representative (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g)) :
    prime _ _ r = (b.val (decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha' r)).val :=
  representativeBlockEquiv_prime seed _ _
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha') p
    (natBlockDraw p b Subtype.val Subtype.val_injective)
    (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha') r

theorem decodedRepresentativeBlockEquiv_multiplicity
    (r : Representative (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g)) :
    Fintype.card (HistoryPairRepresentatives.Fiber _ _ r) =
      multiplicity p (decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha' r) :=
  representativeBlockEquiv_multiplicity seed _ _ _ _ _ _ _ r

include ha ha' in
theorem decoded_unitKernel_product_le_blocks {outside : List ℕ}
    (hs : (blockLeftHistory sources seed V l p b hvalid a f).Supported V outside)
    (ks : (blockRightHistory sources seed V l p b hvalid a' g).Supported V outside) :
    (∏ r, unitKernel _ _ hs ks r) ≤ ∏ q : Block p, 2 / ((b.val q).val : ℝ) :=
  unitKernel_product_le_blocks seed _ _ hs ks
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha') p
    (natBlockDraw p b Subtype.val Subtype.val_injective)
    (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha')

include ha ha' in
theorem decoded_mixedKernel_product_le_blocks {outside : List ℕ}
    (hs : (blockLeftHistory sources seed V l p b hvalid a f).Supported V outside)
    (ks : (blockRightHistory sources seed V l p b hvalid a' g).Supported V outside) :
    (∏ r, mixedKernel _ _ hs ks r) ≤ ∏ q : Block p, 2 / ((b.val q).val : ℝ) :=
  mixedKernel_product_le_blocks seed _ _ hs ks
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha') p
    (natBlockDraw p b Subtype.val Subtype.val_injective)
    (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha')

include ha ha' in

theorem decoded_product_occurrences {M : Type*} [CommMonoid M] (F : ℕ → M) :
    (∏ i : Occurrences (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g), F ((slot _ _ i).value)) =
      ∏ i : Internal seed l ⊕ Internal seed l, F ((expand p b i).val) := by
  let E := pairedInternalEquiv seed _ _
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha')
  calc
    _ = ∏ i, F ((slot _ _ (E i)).value) := (E.prod_comp (fun i => F ((slot _ _ i).value))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact congrArg F (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha' i)

end Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns

end

end OAI
