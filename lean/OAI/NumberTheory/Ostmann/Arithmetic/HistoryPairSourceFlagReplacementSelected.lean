import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementExpectation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
attribute [local instance] Classical.propDecidable
local instance selectedInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

open Filter

theorem selected_decoded_source_scaled_replacement_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {depth : ℕ} (hdepth : 0 < depth) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀v : spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (v:ℕ) ∧
        Real.log (v:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀l,l ≤ depth → ∀(sources : SourceFamily)(seed : List SourceSlot),
      sources = C.sources → seed = Template.initial (2*(Conclusion.bulkSize depth L/2)) depth →
      ∀(p : Pattern (pairedHistoryType seed l))
        (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
        (hvalid : ∀i,(expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
        (a a' : State) (f g : FrequencyChoices (Conclusion.frequencyBound Bs BD Bz depth L) l)
        (ha : Template.Matches (Template.current seed l) a.small)
        (ha' : Template.Matches (Template.current seed l) a'.small)
        (outside : List ℕ)
        (hs : (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f).Supported (Conclusion.frequencyBound Bs BD Bz depth L) outside) (ks : (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g).Supported (Conclusion.frequencyBound Bs BD Bz depth L) outside)
        (hperm : a.small.Perm a'.small),RootGiantsAgree (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) →
      ∀(giants : Bool → PrimeSource)(q : Block p)(mixed : Bool)
        (support : (PairKey (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) → ℤ) → Bool)
        (w : (PairKey (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) → ℤ) → ℝ), (∀x,0≤w x) →
      |decodedSourceMean sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha' hs hperm giants
          (scaledActualTerm mixed (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha').symm q) support w)-
        decodedSourceMean sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha' hs hperm giants
          (scaledSymbolicTerm mixed (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha').symm q) support w)| ≤
        4*decodedSourceMean sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha' hs hperm giants
          (actualFlagTerm (blockLeftHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a f) (blockRightHistory sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid a a' f g ha ha').symm q) support w) := by
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hdepth,
    initial_sources_above_frequencies_eventually d Bs BD Bz hdepth] with L hsep hfreq
  intro E C hG hc hcu hb hd spectator hspec l hl sources seed hsource hseed
    p b hvalid a a' f g ha ha' outside hs ks hperm hroot giants q mixed support w hw
  exact decoded_source_scaled_replacement_le C sources seed (Conclusion.frequencyBound Bs BD Bz depth L) l p b hvalid
    a a' f g ha ha' hs ks hperm hroot hsource hseed
    (hsep E C hG hc hcu hb hd spectator hspec)
    (fun j hj=>(hfreq E C hG hc hcu hb hd j (hj.trans hl)).2)
    giants q mixed support w hw

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
