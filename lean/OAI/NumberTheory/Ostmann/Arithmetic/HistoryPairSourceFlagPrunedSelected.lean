import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagPrunedBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
open HistoryPairSourceFlagPruning HistorySignedResidues HistoryPairRepresentatives HistoryOccurrenceVariables HistorySelectedFlagMassBounds Filter
attribute [local instance] Classical.propDecidable
local instance selectedPrunedBudgetInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_decodedFlagMean_le_pruned_budget_eventually
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
        (hperm : a.small.Perm a'.small) (q : Block p) (A : ℝ) (_hA : 0 ≤ A)
    (support : (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) → ℤ) → Bool)
    (w : (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) → ℤ) → ℝ)
    (_hw : ∀x,(∀i,x i∈(fun j=>prunedSupport ((fun j=>mixedSupport (fun _ : Bool=>C.giant) (decodedRootSources C.sources (Template.initial m depth) V l p b hvalid a f) C.sources (pairedInternalOrigin (Template.initial m depth) l) p ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm).symm j)) j) ((dummyMass (fun _ : Bool=>C.giant) (decodedRootSources C.sources (Template.initial m depth) V l p b hvalid a f) C.sources (pairedInternalOrigin (Template.initial m depth) l) p (decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) q) j)) i) → ∀n∈(prunedSupport (commonCandidates C.sources (pairedInternalOrigin (Template.initial m depth) l)) (blockNaturalWeight C.sources (pairedInternalOrigin (Template.initial m depth) l) p q)),
      0 ≤ w (Function.update x ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ∧
      w (Function.update x ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ≤ A),
    decodedSourceMean C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm (fun _ : Bool=>C.giant)
      (actualFlagTerm (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q) support w)  ≤ 
      HistoryUnnormalizedFlagError.errorBudget A
        (((2*Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q))+
          (Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g):ℕ):ℝ))
        (max 0 (Real.log (envelope (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) V (actualFactorCap Bs BD Bz depth L)))/Real.log 2)
        (HistorySelectedFlagMassBounds.atomCap depth L) (HistorySelectedFlagMassBounds.massCap depth L) (Fintype.card (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))) := by
  filter_upwards [selected_integer_law_bounds_eventually d Bs BD Bz hdepth,
    selected_sources_factorCap_eventually d Bs BD Bz hdepth] with L hL hcap
  intro E C hG hGu hc hcu hb hd m l hl V p b hvalid a a' f g ha ha' outside hs ks hperm q A hA support w hw
  have hbounds := hL E C hG hGu hc hcu hb hd m l hl
    (Fin (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).root.small.length)
    (fun i=>((blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).root.small.get i).origin) p
  have hν := hbounds.2.1 q
  have hμ := hbounds.2.2
    (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f)
      (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))
    (decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) q
  exact decodedFlagMean_le_pruned_budget C.sources (Template.initial m depth) V l p b hvalid
    a a' f g ha ha' hs ks hperm (fun _ : Bool=>C.giant) q (actualFactorCap Bs BD Bz depth L) (atomCap depth L) A (massCap depth L)
    (actualFactorCap_one_le Bs BD Bz depth L) (Real.exp_nonneg _) hA (Real.exp_nonneg _)
    (fun i=>(hμ i).mass) (fun i z _=>(hμ i).atom z) hν.mass (fun n _=>hν.atom n)
    (hcap E C hG hc hcu hb hd) support w hw

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
