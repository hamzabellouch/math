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
local instance costInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

theorem decodedFlagMean_le_exact (giants : Bool → PrimeSource) (q : Block p)
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
    (hw : ∀x,(∀i,x i∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i) → ∀n∈commonCandidates sources (pairedInternalOrigin seed l),
      0≤w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ∧
      w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ))≤A) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (actualFlagTerm (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w) ≤
      A*(∑j : Index (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q),
        (((polynomial (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) j).totalDegree:ℝ)*α*
          Cmass^(Fintype.card (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g))-1)*Cnu+
          β*(max 0 (Real.log (envelope (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) V B))/Real.log 2)*
            Cmass^Fintype.card (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g)))) := by
  rw [decodedSourceMean_eq_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q]
  have hcoordinate : (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm)
      (.inr (.inr q)) = representativeMap
        (blockLeftHistory sources seed V l p b hvalid a f)
        (blockRightHistory sources seed V l p b hvalid a' g)
        ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) := rfl
  simpa only [actualFlagTerm,hcoordinate,Function.update_self,Int.toNat_natCast] using
    shared_family_error_le_exact (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q)
      (fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) (dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) (commonCandidates sources (pairedInternalOrigin seed l)) (blockNaturalWeight sources (pairedInternalOrigin seed l) p q) B α β A Cmass Cnu
      hB hα hβ hA hCmass hCnu
      (fun i z hz=>dummyMass_nonneg giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q i z)
      hmass hatom
      (fun n hn=>commonSample_prime sources (pairedInternalOrigin seed l) ⟨n,hn⟩)
      (fun n hn=>blockNaturalWeight_nonneg sources (pairedInternalOrigin seed l) p q n)
      hνmass hνatom hx hy
      (fun x n=>support (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)))
      (fun x n=>w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ))) hw

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
