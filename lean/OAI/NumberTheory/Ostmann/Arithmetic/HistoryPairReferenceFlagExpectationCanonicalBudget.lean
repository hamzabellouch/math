import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
open HistoryPairReferenceSourceTransport HistoryPairSourceFlagReplacement HistoryPairSourceFlagPruning HistorySignedResidues HistoryPairRepresentatives HistoryOccurrenceVariables HistorySelectedFlagMassBounds Filter
attribute [local instance] Classical.propDecidable
local instance selectedCanonicalFamilyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_canonical_block_family_bound_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {depth : ℕ} (hdepth : 0 < depth) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)  ≤  C.blockBase →
      C.blockBase+favorableBlockWidth L  ≤  Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|  ≤  favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|  ≤  favorableBlockWidth L/16 →
      ∀m l,l  ≤  depth → ∀(V : ℕ → ℕ)
        (p : Pattern (pairedHistoryType (Template.initial m depth) l))
        (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial m depth) l)))
        (hvalid : ∀i,(expand p b i).val ∈ (C.sources (pairedInternalOrigin (Template.initial m depth) l i)).candidates)
        (a a' : State) (f g : FrequencyChoices V l)
        (ha : Template.Matches (Template.current (Template.initial m depth) l) a.small)
        (ha' : Template.Matches (Template.current (Template.initial m depth) l) a'.small)
        (outside : List ℕ)
        (hs : (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).Supported V outside)
        (ks : (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g).Supported V outside)
        (hperm : a.small.Perm a'.small),
    canonicalSourceMean
      (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
      (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks)
      p (natBlockDraw p b Subtype.val Subtype.val_injective)
      (blockReferences_slot_values C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs ks)
      (blockReferences_root_perm C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs ks hperm)
      (fun _ : Bool=>C.giant)
      (family (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
        (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks)) ≤
    ∑q : Block p,
      HistoryUnnormalizedFlagError.errorBudget 1
        (((2*Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q))+
          (Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g):ℕ):ℝ))
        (max 0 (Real.log (envelope (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) V (actualFactorCap Bs BD Bz depth L)))/Real.log 2)
        (HistorySelectedFlagMassBounds.atomCap depth L) (HistorySelectedFlagMassBounds.massCap depth L) (Fintype.card (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))) := by
  filter_upwards [selected_block_family_bound_eventually d Bs BD Bz hdepth] with L hL
  intro E C hG hGu hc hcu hb hd m l hl V p b hvalid a a' f g ha ha' outside hs ks hperm
  have heq := decodedSourceMean_eq_canonical C.sources (Template.initial m depth) V l p b hvalid
    a a' f g ha ha' hs ks hperm (fun _ : Bool=>C.giant)
    (family (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
      (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks))
  exact heq.symm.trans_le (hL E C hG hGu hc hcu hb hd m l hl V p b hvalid a a' f g ha ha' outside hs ks hperm)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
