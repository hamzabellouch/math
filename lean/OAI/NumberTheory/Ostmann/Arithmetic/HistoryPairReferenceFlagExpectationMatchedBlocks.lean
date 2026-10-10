import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagMatchedBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
open HistoryPairBulkCoordinates HistoryPairReferenceSourceTransport HistoryPairSourceFlagReplacement HistoryPairSourceFlagPruning HistorySignedResidues HistoryPairRepresentatives HistoryOccurrenceVariables HistorySelectedFlagMassBounds Filter
attribute [local instance] Classical.propDecidable
local instance selectedCanonicalMatchedFamilyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

section MatchedFamily
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E : DecodedDraw sources seed V outside l)
  (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
  (hv : ∀i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value = expand p b i)
  (e : RootMatching D.history E.history) (giants : Bool → PrimeSource)

theorem canonicalSourceMeanMatched_family :
    canonicalSourceMeanMatched D E p b hv e giants (family D E) =
      ∑q : Block p, canonicalSourceMeanMatched D E p b hv e giants
        (actualFlagTerm D.history E.history D.supported E.supported
          ((typedBlockEquiv D E p b hv).symm q) (fun _ => true) (fun _ => 1)) := by
  have hf : family D E = fun x => ∑q : Block p,
      actualFlagTerm D.history E.history D.supported E.supported
        ((typedBlockEquiv D E p b hv).symm q) (fun _ => true) (fun _ => 1) x := by
    funext x
    have he := (typedBlockEquiv D E p b hv).symm.sum_comp
      (fun r => ∑j : Index D.history E.history r,
        flagError (polynomial D.history E.history D.supported E.supported r j) x
          (x (representativeMap D.history E.history r)).toNat)
    simpa only [family,actualFlagTerm,ite_true,one_mul] using he.symm
  rw [hf]
  unfold canonicalSourceMeanMatched
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end MatchedFamily

theorem selected_canonical_block_family_bound_matched_eventually
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
        (e : RootMatching (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f)
          (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g)),
    canonicalSourceMeanMatched
      (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
      (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks)
      p (natBlockDraw p b Subtype.val Subtype.val_injective)
      (blockReferences_slot_values C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs ks)
      e
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
  filter_upwards [selected_integer_law_bounds_eventually d Bs BD Bz hdepth,
    selected_sources_factorCap_eventually d Bs BD Bz hdepth] with L hL hcap
  intro E C hG hGu hc hcu hb hd m l hl V p b hvalid a a' f g ha ha' outside hs ks e
  erw [canonicalSourceMeanMatched_family]
  apply Finset.sum_le_sum
  intro q _
  have hbounds := hL E C hG hGu hc hcu hb hd m l hl
    (Fin (Template.current (Template.initial m depth) l).length)
    (fun i => ((Template.current (Template.initial m depth) l).get i).origin) p
  have hν := hbounds.2.1 q
  have hμ := hbounds.2.2
    (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f)
      (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))
    (typedSourceEquivMatched
      (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
      (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks)
      p (natBlockDraw p b Subtype.val Subtype.val_injective)
      (blockReferences_slot_values C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs ks) e) q
  exact canonicalMatchedFlagMean_le_pruned_budget
    (blockLeftReference C.sources (Template.initial m depth) V l p b hvalid a f ha hs)
    (blockRightReference C.sources (Template.initial m depth) V l p b hvalid a' g ha' ks)
    p (natBlockDraw p b Subtype.val Subtype.val_injective)
    (blockReferences_slot_values C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs ks)
    e (fun _ : Bool => C.giant) q (actualFactorCap Bs BD Bz depth L)
    (atomCap depth L) (massCap depth L)
    (actualFactorCap_one_le Bs BD Bz depth L) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (fun i => (hμ i).mass) (fun i z _ => (hμ i).atom z)
    hν.mass (fun n _ => hν.atom n) (hcap E C hG hc hcu hb hd)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
