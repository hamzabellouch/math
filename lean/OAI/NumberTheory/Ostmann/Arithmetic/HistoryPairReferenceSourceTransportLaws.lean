import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLaws

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns HistoryPairSourceLaws
local instance sourceTransportLawsInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
attribute [local instance] Classical.propDecidable

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
  (p : Pattern (pairedHistoryType seed l)) (b b' : BlockDraw p ℕ)
  (hv : ∀ i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value=expand p b i)
  (hv' : ∀ i, (slot D'.history E'.history (pairedOccurrenceEquiv D' E' i)).value=expand p b' i)
  (hperm : D.history.root.small.Perm E.history.root.small)
  (hperm' : D'.history.root.small.Perm E'.history.root.small)

def templateRootSources (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    Fin (Template.current seed l).length → PrimeSource :=
  fun i=>sources (((Template.current seed l).get i).origin)

def actualRootSources (D : DecodedDraw sources seed V outside l) :
    Fin D.history.root.small.length → PrimeSource :=
  fun i=>sources ((D.history.root.small.get i).origin)

def canonicalSourceMean (giants : Bool → PrimeSource)
    (F : (PairKey D.history E.history → ℤ) → ℝ) : ℝ :=
  ∑ x : ∀i,mixedCarrier giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i,
    (∏i,mixedWeight giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (x i))*
      F ((fun i=>mixedValue giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (x i)) ∘
        (typedSourceEquiv D E p b hv hperm).symm)

theorem canonicalSourceMean_transport (giants : Bool → PrimeSource)
    (F : (PairKey D'.history E'.history → ℤ) → ℝ) :
    canonicalSourceMean D E p b hv hperm giants
      (fun x=>F (x ∘ (pairedBlockEquiv D E D' E' hp).symm))=
    canonicalSourceMean D' E' p b' hv' hperm' giants F := by
  unfold canonicalSourceMean
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact congrArg F (typedSourceEquiv_pullSample D E D' E' hp p b b' hv hv' hperm hperm' _)

theorem root_law_eq (giants : Bool → PrimeSource)
    (i : TypedSourceIndex p) :
    let e := Equiv.sumCongr (Equiv.refl Bool) (Equiv.sumCongr (rootPosition D) (Equiv.refl (Block p)))
    mixedSupport giants (actualRootSources D) sources (pairedInternalOrigin seed l) p (e i)=
      mixedSupport giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i ∧
    mixedMass giants (actualRootSources D) sources (pairedInternalOrigin seed l) p (e i)=
      mixedMass giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i := by
  rcases i with t | i | q
  · exact ⟨rfl,rfl⟩
  · dsimp only [Equiv.sumCongr_apply,Equiv.refl_apply,Sum.map_inr,Sum.map_inl]
    have he : actualRootSources D (rootPosition D i)=templateRootSources sources seed l i :=
      rootPosition_source D i
    exact ⟨congrArg (fun S : PrimeSource => integerSupport (fun a : S.Sample => (a.val : ℤ))) he,
      congrArg (fun S : PrimeSource => integerWeight (fun a : S.Sample => (a.val : ℤ)) S.law.mass) he⟩
  · exact ⟨rfl,rfl⟩

theorem actual_source_mean_eq_canonical (giants : Bool → PrimeSource)
    (F : (PairKey D.history E.history → ℤ) → ℝ) :
    let e := blockSourceEquiv D.history E.history D.supported hperm (typedBlockEquiv D E p b hv)
    (∑ x : ∀i,mixedCarrier giants (actualRootSources D) sources (pairedInternalOrigin seed l) p i,
      (∏i,mixedWeight giants (actualRootSources D) sources (pairedInternalOrigin seed l) p i (x i))*
        F (fun j=>mixedValue giants (actualRootSources D) sources (pairedInternalOrigin seed l) p (e.symm j) (x (e.symm j))))=
      canonicalSourceMean D E p b hv hperm giants F := by
  dsimp only
  rw [mixed_product_sum_reindex]
  unfold canonicalSourceMean
  simp only [Function.comp_def]
  rw [mixed_product_sum_reindex]
  have hidx (j : PairKey D.history E.history) :
      (blockSourceEquiv D.history E.history D.supported hperm (typedBlockEquiv D E p b hv)).symm j=
      (Equiv.sumCongr (Equiv.refl Bool) (Equiv.sumCongr (rootPosition D) (Equiv.refl (Block p))))
        ((typedSourceEquiv D E p b hv hperm).symm j) := by
    obtain ⟨i,rfl⟩ := (typedSourceEquiv D E p b hv hperm).surjective j
    simp only [Equiv.symm_apply_apply]
    apply (blockSourceEquiv D.history E.history D.supported hperm (typedBlockEquiv D E p b hv)).injective
    rw [Equiv.apply_symm_apply]
    rcases i with t | i | q <;> rfl
  have hS : (fun j=>mixedSupport giants (actualRootSources D) sources (pairedInternalOrigin seed l) p
      ((blockSourceEquiv D.history E.history D.supported hperm (typedBlockEquiv D E p b hv)).symm j))=
      (fun j=>mixedSupport giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p
        ((typedSourceEquiv D E p b hv hperm).symm j)) := by
    funext j
    rw [hidx]
    exact (root_law_eq D p giants _).1
  rw [hS]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [hidx]
  exact congrFun (root_law_eq D p giants _).2 (x j)

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
