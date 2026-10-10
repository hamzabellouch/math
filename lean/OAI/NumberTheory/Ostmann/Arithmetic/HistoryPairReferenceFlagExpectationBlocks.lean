import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagPruned

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
attribute [local instance] Classical.propDecidable
local instance referenceBlocksInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

open HistoryPairSourceFlagReplacement HistoryPairFlagReplacementUnnormalized HistoryPairRepresentatives HistoryOccurrenceVariables

def blockLeftReference : DecodedDraw sources seed V outside l where
  root := a
  choices := blockLeftChoices sources seed V l p b hvalid f
  sourceMatch := ha
  supported := hs

def blockRightReference : DecodedDraw sources seed V outside l where
  root := a'
  choices := blockRightChoices sources seed V l p b hvalid g
  sourceMatch := ha'
  supported := ks

theorem decodedSourceMean_sum {γ : Type*} [Fintype γ]
    (giants : Bool → PrimeSource) (F : γ → (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants (fun x=>∑i,F i x)=
      ∑i,decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants (F i) := by
  unfold decodedSourceMean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem block_family_eq (x : PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) :
    family (blockLeftReference sources seed V l p b hvalid a f ha hs)
      (blockRightReference sources seed V l p b hvalid a' g ha' ks) x=
    ∑q : Block p,actualFlagTerm (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks
      ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q)
      (fun _=>true) (fun _=>1) x := by
  have he := (decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm.sum_comp
    (fun r=>∑j : Index (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) r,flagError (polynomial (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks r j) x
      (x (representativeMap (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) r)).toNat)
  simpa +instances only [family,blockLeftReference,blockRightReference,actualFlagTerm,ite_true,one_mul,
    DecodedDraw.history,blockLeftHistory,blockRightHistory] using he.symm

theorem decodedSourceMean_family (giants : Bool → PrimeSource) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (family (blockLeftReference sources seed V l p b hvalid a f ha hs)
        (blockRightReference sources seed V l p b hvalid a' g ha' ks))=
    ∑q : Block p,decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (actualFlagTerm (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks
        ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q)
        (fun _=>true) (fun _=>1)) := by
  have hf := funext (block_family_eq sources seed V l p b hvalid a a' f g ha ha' hs ks)
  rw [hf]
  exact decodedSourceMean_sum sources seed V l p b hvalid a a' f g ha ha' hs hperm giants _

end Decoded
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
