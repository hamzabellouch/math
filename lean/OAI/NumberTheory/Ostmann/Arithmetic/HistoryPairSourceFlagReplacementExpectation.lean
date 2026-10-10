import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementMean

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
local instance expectationInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

section Decoded
variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz depth L E) (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
variable (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
  (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)
variable {outside : List ℕ} (hs : ((blockLeftHistory sources seed V l p b hvalid a f)).Supported V outside) (ks : ((blockRightHistory sources seed V l p b hvalid a' g)).Supported V outside)
  (hperm : a.small.Perm a'.small) (hroot : @RootGiantsAgree l (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g))

include hroot in

theorem decoded_source_scaled_replacement_le
    (hsource : sources = C.sources)
    (hseed : seed = Template.initial (2*(Conclusion.bulkSize depth L/2)) depth)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hV : ∀j ≤ l,∀sourceOrigin,(C.sources sourceOrigin).AboveFrequency (V j))
    (giants : Bool → PrimeSource) (q : Block p) (mixed : Bool)
    (support : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → Bool)
    (w : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) (hw : ∀x,0≤w x) :
    |decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
        (scaledActualTerm mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w)-
      decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
        (scaledSymbolicTerm mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w)| ≤
      4*decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
        (actualFlagTerm (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w) := by
  rw [decodedSourceMean_eq_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q,
    decodedSourceMean_eq_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q,
    decodedSourceMean_eq_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q]
  apply weighted_update_abs_sub_le
  · intro i z hz
    exact dummyMass_nonneg giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q i z
  · intro n hn
    exact blockNaturalWeight_nonneg sources (pairedInternalOrigin seed l) p q n
  · intro x hx n hn hxmass hnν
    have hh := decoded_scaled_error_of_nonzero_weights C sources seed V l p b hvalid
      a a' f g ha ha' hs ks hperm hroot hsource hseed hsep hV giants q mixed x n hxmass hnν
    exact scaled_terms_update_error mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w x n (hw _) hh

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
