import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportMatchedLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagPrunedBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
open HistoryPairReferenceSourceTransport HistoryPairBulkCoordinates
open HistoryPairSourceFlagPruning HistoryPairFlagReplacementUnnormalized HistoryPairRepresentatives HistoryOccurrenceVariables
attribute [local instance] Classical.propDecidable
local instance matchedBudgetInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E : DecodedDraw sources seed V outside l)
  (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
  (hv : ∀i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value = expand p b i)
  (e : RootMatching D.history E.history) (giants : Bool → PrimeSource)

def matchedSourceSupport : PairKey D.history E.history → Finset ℤ :=
  fun j => mixedSupport giants (templateRootSources sources seed l) sources
    (pairedInternalOrigin seed l) p ((typedSourceEquivMatched D E p b hv e).symm j)

def matchedDummyMass (q : Block p) : PairKey D.history E.history → ℤ → ℝ :=
  dummyMass giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p
    (typedSourceEquivMatched D E p b hv e) q

theorem canonicalSourceMeanMatched_eq_update (q : Block p)
    (F : (PairKey D.history E.history → ℤ) → ℝ) :
    canonicalSourceMeanMatched D E p b hv e giants F =
      ∑x ∈ Fintype.piFinset (matchedSourceSupport D E p b hv e giants),
        (∏j, matchedDummyMass D E p b hv e giants q j (x j)) *
          ∑n ∈ commonCandidates sources (pairedInternalOrigin seed l),
            blockNaturalWeight sources (pairedInternalOrigin seed l) p q n *
              F (Function.update x (typedSourceEquivMatched D E p b hv e (.inr (.inr q))) (n:ℤ)) := by
  unfold canonicalSourceMeanMatched
  simp only [Function.comp_def]
  rw [mixed_product_sum_reindex]
  exact mixed_product_sum_update giants (templateRootSources sources seed l) sources
    (pairedInternalOrigin seed l) p (typedSourceEquivMatched D E p b hv e) q F

theorem matched_dummy_small_abs_le (q : Block p) (B : ℝ)
    (hcap : ∀i, ∀v : (sources i).Sample, (sources i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B) :
    (∀i : Fin D.history.root.small.length ⊕ InternalKey D.history, ∀z : ℤ,
      matchedDummyMass D E p b hv e giants q (leftMap D.history E.history (.inr i)) z ≠ 0 → |(z:ℝ)| ≤ B) ∧
    (∀i : Fin E.history.root.small.length ⊕ InternalKey E.history, ∀z : ℤ,
      matchedDummyMass D E p b hv e giants q (rightMap D.history E.history (.inr i)) z ≠ 0 → |(z:ℝ)| ≤ B) := by
  constructor
  · intro i z hz
    apply dummyMass_non_giant_abs_le giants (templateRootSources sources seed l) sources
      (pairedInternalOrigin seed l) p (typedSourceEquivMatched D E p b hv e) q B
      (fun i => hcap _) hcap _ ?_ z hz
    intro t he
    have he' := congrArg Subtype.val he
    rcases i with i | i <;>
      change (Sum.inr _ : Bool ⊕ (ℕ × ℤ)) = Sum.inl t at he' <;> cases he'
  · intro i z hz
    apply dummyMass_non_giant_abs_le giants (templateRootSources sources seed l) sources
      (pairedInternalOrigin seed l) p (typedSourceEquivMatched D E p b hv e) q B
      (fun i => hcap _) hcap _ ?_ z hz
    intro t he
    have he' := congrArg Subtype.val he
    rcases i with i | i <;>
      change (Sum.inr _ : Bool ⊕ (ℕ × ℤ)) = Sum.inl t at he' <;> cases he'

theorem canonicalMatchedFlagMean_le_pruned_budget (q : Block p)
    (B atom mass : ℝ) (hB : 1 ≤ B) (hatom0 : 0 ≤ atom) (hmass0 : 0 ≤ mass)
    (hmass : ∀i, ∑z ∈ matchedSourceSupport D E p b hv e giants i,
      matchedDummyMass D E p b hv e giants q i z ≤ mass)
    (hatom : ∀i z, z ∈ matchedSourceSupport D E p b hv e giants i →
      matchedDummyMass D E p b hv e giants q i z ≤ atom)
    (hνmass : ∑n ∈ commonCandidates sources (pairedInternalOrigin seed l),
      blockNaturalWeight sources (pairedInternalOrigin seed l) p q n ≤ mass)
    (hνatom : ∀n ∈ commonCandidates sources (pairedInternalOrigin seed l),
      blockNaturalWeight sources (pairedInternalOrigin seed l) p q n ≤ atom)
    (hcap : ∀i, ∀v : (sources i).Sample, (sources i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B) :
    canonicalSourceMeanMatched D E p b hv e giants
      (actualFlagTerm D.history E.history D.supported E.supported
        ((typedBlockEquiv D E p b hv).symm q) (fun _ => true) (fun _ => 1)) ≤
      HistoryUnnormalizedFlagError.errorBudget 1
        (((2*Fintype.card (Fiber D.history E.history ((typedBlockEquiv D E p b hv).symm q))+
          (Fintype.card (Fiber D.history E.history ((typedBlockEquiv D E p b hv).symm q)))^2:ℕ):ℝ))
        (((4*degreeBudget D.history E.history:ℕ):ℝ))
        (max 0 (Real.log (envelope D.history E.history V B))/Real.log 2)
        atom mass (Fintype.card (PairKey D.history E.history)) := by
  rw [canonicalSourceMeanMatched_eq_update D E p b hv e giants q]
  rw [double_sum_prunedSupport]
  have hsmall := matched_dummy_small_abs_le D E p b hv e giants q B hcap
  have hcoordinate : typedSourceEquivMatched D E p b hv e (.inr (.inr q)) =
      representativeMap D.history E.history ((typedBlockEquiv D E p b hv).symm q) := rfl
  simpa only [actualFlagTerm,hcoordinate,Function.update_self,Int.toNat_natCast,
    HistoryUnnormalizedFlagError.errorBudget] using
    shared_family_error_le D.history E.history D.supported E.supported
      ((typedBlockEquiv D E p b hv).symm q)
      (fun j => prunedSupport (matchedSourceSupport D E p b hv e giants j)
        (matchedDummyMass D E p b hv e giants q j))
      (matchedDummyMass D E p b hv e giants q)
      (prunedSupport (commonCandidates sources (pairedInternalOrigin seed l))
        (blockNaturalWeight sources (pairedInternalOrigin seed l) p q))
      (blockNaturalWeight sources (pairedInternalOrigin seed l) p q) B atom atom 1 mass mass
      hB hatom0 hatom0 (by norm_num) hmass0 hmass0
      (fun i z _ => dummyMass_nonneg giants (templateRootSources sources seed l) sources
        (pairedInternalOrigin seed l) p (typedSourceEquivMatched D E p b hv e) q i z)
      (fun i => prunedSupport_mass_le _ _ _ (hmass i))
      (fun i z hz => hatom i z (mem_prunedSupport _ _ _ |>.mp hz).1)
      (fun n hn => commonSample_prime sources (pairedInternalOrigin seed l)
        ⟨n,(mem_prunedSupport _ _ _ |>.mp hn).1⟩)
      (fun n _ => blockNaturalWeight_nonneg sources (pairedInternalOrigin seed l) p q n)
      (prunedSupport_mass_le _ _ _ hνmass)
      (fun n hn => hνatom n (mem_prunedSupport _ _ _ |>.mp hn).1)
      (fun i z hz => hsmall.1 i z (mem_prunedSupport _ _ _ |>.mp hz).2)
      (fun i z hz => hsmall.2 i z (mem_prunedSupport _ _ _ |>.mp hz).2)
      (fun _ _ => true) (fun _ _ => 1) (by intro x hx n hn; constructor <;> norm_num)

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
