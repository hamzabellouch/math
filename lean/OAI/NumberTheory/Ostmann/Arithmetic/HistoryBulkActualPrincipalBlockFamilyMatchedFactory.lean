import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedSelectedData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryPairPattern HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMatchedFactoryInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (s : ℕ) (hlen : outside.length=2*s) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (independent : Bool)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

def matchedPrincipalFamily : MatchedPrincipalBlockFamily C outside l f g p where
  active o := (selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).isSome
  reference o ho := ((selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).get ho).blockReference
  leftRootFrequency := v.val
  rightRootFrequency := v.val
  leftRootFrequency_eq := fun _ _=>rfl
  rightRootFrequency_eq := fun _ _=>rfl
  leftFrequency_eq := fun _ _=>rfl
  rightFrequency_eq := fun _ _=>rfl
  permutation := selectedLeafPermutation C l σ
  rootAligned o ho t := ((selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).get ho).rootAligned t
  principal o ho := ((selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).get ho).principalData hcell s hlen hprime hV independent

theorem matchedPrincipalFamily_reference_giants
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : (matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell s hlen hprime hV
      independent v f g).active o) :
    RootGiantsAgree
      ((matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell s hlen hprime hV
        independent v f g).reference o ho).left.history
      ((matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell s hlen hprime hV
        independent v f g).reference o ho).right.history :=
  ((selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).get ho).giants

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
