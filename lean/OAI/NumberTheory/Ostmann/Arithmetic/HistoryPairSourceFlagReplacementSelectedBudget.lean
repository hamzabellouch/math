import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementBudget
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
open HistoryPairRepresentatives HistoryOccurrenceVariables HistorySelectedFlagMassBounds Filter
attribute [local instance] Classical.propDecidable
local instance selectedBudgetInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_decodedFlagMean_le_budget_eventually
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
        (hperm : a.small.Perm a'.small) (q : Block p) (B A : ℝ) (_hB : 1 ≤ B) (_hA : 0 ≤ A)
    (_hx : ∀i : Fin (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).root.small.length ⊕ InternalKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f),
      ∀z∈(fun j=>mixedSupport (fun _ : Bool=>C.giant) (decodedRootSources C.sources (Template.initial m depth) V l p b hvalid a f) C.sources (pairedInternalOrigin (Template.initial m depth) l) p ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm).symm j)) (leftMap (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) (.inr i)),|(z:ℝ)| ≤ B)
    (_hy : ∀i : Fin (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g).root.small.length ⊕ InternalKey (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g),
      ∀z∈(fun j=>mixedSupport (fun _ : Bool=>C.giant) (decodedRootSources C.sources (Template.initial m depth) V l p b hvalid a f) C.sources (pairedInternalOrigin (Template.initial m depth) l) p ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm).symm j)) (rightMap (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) (.inr i)),|(z:ℝ)| ≤ B)
    (support : (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) → ℤ) → Bool)
    (w : (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) → ℤ) → ℝ)
    (_hw : ∀x,(∀i,x i∈(fun j=>mixedSupport (fun _ : Bool=>C.giant) (decodedRootSources C.sources (Template.initial m depth) V l p b hvalid a f) C.sources (pairedInternalOrigin (Template.initial m depth) l) p ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i) → ∀n∈commonCandidates C.sources (pairedInternalOrigin (Template.initial m depth) l),
      0 ≤ w (Function.update x ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ∧
      w (Function.update x ((decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ≤ A),
    decodedSourceMean C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm (fun _ : Bool=>C.giant)
      (actualFlagTerm (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q) support w)  ≤ 
      HistoryUnnormalizedFlagError.errorBudget A
        (((2*Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q))+
          (Fintype.card (Fiber (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha').symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g):ℕ):ℝ))
        (max 0 (Real.log (envelope (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g) V B))/Real.log 2)
        (HistorySelectedFlagMassBounds.atomCap depth L) (HistorySelectedFlagMassBounds.massCap depth L) (Fintype.card (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f) (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))) := by
  filter_upwards [selected_integer_law_bounds_eventually d Bs BD Bz hdepth] with L hL
  intro E C hG hGu hc hcu hb hd m l hl V p b hvalid a a' f g ha ha' outside hs ks hperm q B A hB hA
    hx hy support w hw
  have hbounds := hL E C hG hGu hc hcu hb hd m l hl
    (Fin (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).root.small.length)
    (fun i=>((blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f).root.small.get i).origin) p
  have hν := hbounds.2.1 q
  have hμ := hbounds.2.2
    (PairKey (blockLeftHistory C.sources (Template.initial m depth) V l p b hvalid a f)
      (blockRightHistory C.sources (Template.initial m depth) V l p b hvalid a' g))
    (decodedSourceEquiv C.sources (Template.initial m depth) V l p b hvalid a a' f g ha ha' hs hperm) q
  exact decodedFlagMean_le_budget C.sources (Template.initial m depth) V l p b hvalid
    a a' f g ha ha' hs ks hperm (fun _ : Bool=>C.giant) q B (atomCap depth L) A (massCap depth L)
    hB (Real.exp_nonneg _) hA (Real.exp_nonneg _)
    (fun i=>(hμ i).mass) (fun i z _=>(hμ i).atom z) hν.mass (fun n _=>hν.atom n)
    hx hy support w hw

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
