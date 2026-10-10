import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagEnvelope
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagPruning
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementExpectation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorBasic

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
local instance prunedBudgetInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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

open HistoryPairSourceFlagPruning HistoryPairFlagReplacementUnnormalized HistoryPairRepresentatives HistoryOccurrenceVariables

theorem decodedFlagMean_le_pruned_budget (giants : Bool → PrimeSource) (q : Block p)
    (B atom A mass : ℝ) (hB : 1 ≤ B) (hatom0 : 0 ≤ atom)
    (hA : 0 ≤ A) (hmass0 : 0 ≤ mass)
    (hmass : ∀i,∑z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i,(dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) i z ≤ mass)
    (hatom : ∀i z,z∈(fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) i → (dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) i z ≤ atom)
    (hνmass : ∑n∈commonCandidates sources (pairedInternalOrigin seed l),(blockNaturalWeight sources (pairedInternalOrigin seed l) p q) n ≤ mass)
    (hνatom : ∀n∈commonCandidates sources (pairedInternalOrigin seed l),(blockNaturalWeight sources (pairedInternalOrigin seed l) p q) n ≤ atom)
    (hcap : ∀ i, ∀ v : (sources i).Sample,
      (sources i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B)
    (support : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → Bool)
    (w : (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ)
    (hw : ∀x,(∀i,x i∈(fun j=>prunedSupport ((fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) j) ((dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) j)) i) → ∀n∈(prunedSupport (commonCandidates sources (pairedInternalOrigin seed l)) (blockNaturalWeight sources (pairedInternalOrigin seed l) p q)),
      0 ≤ w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ∧
      w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)) ≤ A) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants
      (actualFlagTerm (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) support w)  ≤ 
      HistoryUnnormalizedFlagError.errorBudget A
        (((2*Fintype.card (Fiber (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q))+
          (Fintype.card (Fiber (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g):ℕ):ℝ))
        (max 0 (Real.log (envelope (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) V B))/Real.log 2)
        atom mass (Fintype.card (PairKey (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g))) := by
  rw [decodedSourceMean_eq_update sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q]
  rw [double_sum_prunedSupport]
  have hsmall := decoded_dummy_small_abs_le sources seed V l p b hvalid a a' f g ha ha' hs hperm giants q B hcap
  have hcoordinate : (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm)
      (.inr (.inr q)) = representativeMap
        (blockLeftHistory sources seed V l p b hvalid a f)
        (blockRightHistory sources seed V l p b hvalid a' g)
        ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) := rfl
  simpa only [actualFlagTerm,hcoordinate,Function.update_self,Int.toNat_natCast,HistoryUnnormalizedFlagError.errorBudget] using
    shared_family_error_le (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) hs ks ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q)
      (fun j=>prunedSupport ((fun j=>mixedSupport giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm).symm j)) j) ((dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) j)) (dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q) (prunedSupport (commonCandidates sources (pairedInternalOrigin seed l)) (blockNaturalWeight sources (pairedInternalOrigin seed l) p q)) (blockNaturalWeight sources (pairedInternalOrigin seed l) p q) B atom atom A mass mass
      hB hatom0 hatom0 hA hmass0 hmass0
      (fun i z hz=>dummyMass_nonneg giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q i z)
      (fun i=>prunedSupport_mass_le _ _ _ (hmass i))
      (fun i z hz=>hatom i z (mem_prunedSupport _ _ _ |>.mp hz).1)
      (fun n hn=>commonSample_prime sources (pairedInternalOrigin seed l) ⟨n,(mem_prunedSupport _ _ _ |>.mp hn).1⟩)
      (fun n hn=>blockNaturalWeight_nonneg sources (pairedInternalOrigin seed l) p q n)
      (prunedSupport_mass_le _ _ _ hνmass)
      (fun n hn=>hνatom n (mem_prunedSupport _ _ _ |>.mp hn).1)
      (fun i z hz=>hsmall.1 i z (mem_prunedSupport _ _ _ |>.mp hz).2)
      (fun i z hz=>hsmall.2 i z (mem_prunedSupport _ _ _ |>.mp hz).2)
      (fun x n=>support (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ)))
      (fun x n=>w (Function.update x ((decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) (.inr (.inr q))) (n:ℤ))) hw

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
