import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupport

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
local instance basicInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

theorem decoded_scaled_error_of_nonzero_weights
    (hsource : sources = C.sources)
    (hseed : seed = Template.initial (2*(Conclusion.bulkSize depth L/2)) depth)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hV : ∀j ≤ l,∀sourceOrigin,(C.sources sourceOrigin).AboveFrequency (V j))
    (giants : Bool → PrimeSource) (q : Block p) (mixed : Bool)
    (x : PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) (n : ℕ)
    (hx : (∏ j, dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q j (x j)) ≠ 0)
    (hn : blockNaturalWeight sources (pairedInternalOrigin seed l) p q n ≠ 0) :
    (n:ℝ)*|actualProbability mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) n
      (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ))-
        symbolicKernel mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) n| ≤
      4*∑j : Index (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q),flagError (polynomial (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) j)
        (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) n := by
  have hx' := decoded_updated_smallSourceSamples sources seed V l p b hvalid
    a a' f g ha ha' hs hperm giants q x n hx hn
  rw (occs := .pos [1]) [hsource] at hx'
  have hh := scaled_error_of_source_samples C hsep mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g)
    (by rw [←hseed]; exact blockLeftLabels sources seed V l p b hvalid a f ha)
    (by rw [←hseed]; exact blockRightLabels sources seed V l p b hvalid a' g ha') hs ks hroot
    _ hx' ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) n (by simp only [Function.update_self]) hV
  exact hh

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
