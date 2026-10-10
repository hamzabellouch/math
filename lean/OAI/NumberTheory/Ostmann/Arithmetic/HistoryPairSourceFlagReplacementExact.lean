import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementCost
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementSelected

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
local instance exactInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

open HistoryPairFlagReplacementUnnormalized HistoryPairRepresentatives HistoryOccurrenceVariables

include hroot in

theorem decoded_source_scaled_replacement_le_exact
    (hsource : sources = C.sources)
    (hseed : seed = Template.initial (2*(Conclusion.bulkSize depth L/2)) depth)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hV : ∀j ≤ l,∀sourceOrigin,(C.sources sourceOrigin).AboveFrequency (V j))
    (mixed : Bool) (giants : Bool → PrimeSource) (q : Block p)
    (B α β A Cmass Cnu : ℝ) (hB : 1≤B) (hα : 0≤α) (hβ : 0≤β)
    (hA : 0≤A) (hCmass : 0≤Cmass) (hCnu : 0≤Cnu)
    (hmass : ∀i,∑z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i,(dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) i z≤Cmass)
    (hatom : ∀i z,z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i → (dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) i z≤α)
    (hνmass : ∑n∈commonCandidates sources (pairedInternalOrigin seed l),(blockNaturalWeight sources (pairedInternalOrigin seed l) p q) n≤Cnu)
    (hνatom : ∀n∈commonCandidates sources (pairedInternalOrigin seed l),(blockNaturalWeight sources (pairedInternalOrigin seed l) p q) n≤β)
    (hx : ∀i : Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length ⊕ InternalKey (blockLeftHistory sources seed V l p b hvalid a f),
      ∀z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) (leftMap (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) (.inr i)),|(z:ℝ)|≤B)
    (hy : ∀i : Fin (blockRightHistory sources seed V l p b hvalid a' g).root.small.length ⊕ InternalKey (blockRightHistory sources seed V l p b hvalid a' g),
      ∀z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) (rightMap (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) (.inr i)),|(z:ℝ)|≤B)
    (support : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → Bool)
    (w : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ)
    (hnonneg : ∀x,0≤w x)
    (hw : ∀x,(∀i,x i∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i) → ∀n∈commonCandidates sources (pairedInternalOrigin seed l),
      0≤w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ∧
      w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ))≤A) :
    |decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (scaledActualTerm mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w)-
      decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (scaledSymbolicTerm mixed (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w)| ≤
      (4*A)*(∑j : Index (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q),
        (((polynomial (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) j).totalDegree:ℝ)*α*
          Cmass^(Fintype.card (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g))-1)*Cnu+
          β*(max 0 (Real.log (envelope (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) V B))/Real.log 2)*
            Cmass^Fintype.card (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g)))) := by
  have he := decoded_source_scaled_replacement_le C sources seed V l p b hvalid
    a a' f g ha ha' hs ks hperm hroot hsource hseed hsep hV giants q mixed support w hnonneg
  have hf := decodedFlagMean_le_exact sources seed V l p b hvalid a a' f g ha ha' hs ks hperm
    giants q B α β A Cmass Cnu hB hα hβ hA hCmass hCnu hmass hatom hνmass hνatom
    hx hy support w hw
  convert he.trans (mul_le_mul_of_nonneg_left hf (by norm_num : 0 ≤ (4:ℝ))) using 1
  ring

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
