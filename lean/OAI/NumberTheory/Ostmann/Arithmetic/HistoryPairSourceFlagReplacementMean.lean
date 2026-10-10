import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementTerms

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
local instance meanInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

def decodedSourceMean (giants : Bool → PrimeSource) (F : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) : ℝ :=
  ∑ x : ∀i,mixedCarrier giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p i,
    (∏i,mixedWeight giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p i (x i))*
      F (fun j=>mixedValue giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j) (x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)))

theorem decodedSourceMean_eq_update (giants : Bool → PrimeSource) (q : Block p)
    (F : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants F =
      ∑x∈Fintype.piFinset (fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)),
        (∏j,dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q j (x j))*
          ∑n∈commonCandidates sources (pairedInternalOrigin seed l),blockNaturalWeight sources (pairedInternalOrigin seed l) p q n*
            F (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) := by
  exact decoded_product_sum_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q F

theorem decodedSourceMean_sub (giants : Bool → PrimeSource)
    (F G : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants (fun x=>F x-G x) =
      decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants F-
        decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants G := by
  simp only [decodedSourceMean,mul_sub,Finset.sum_sub_distrib]

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
