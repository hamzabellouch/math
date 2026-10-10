import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion CanonicalHistoryLeafBulk HistoryPairBulkTransport HistoryBulkProducts
open HistoryBulkDiagramParameters HistoryBulkSpectatorReferenceRaw
open HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry
open HistoryCRTIntegration HistoryBulkResidueNormSum HistoryPrincipalIntegralAverage
open HistoryBulkReferenceTests HistorySignedSpectatorCRT ResidueHaar
open HistorySignedResidueFactorization HistoryBulkReferencePeriodicMeanSource
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
namespace Frame

def mixedBMean (r : Frame (l:=l) C outside) (x : Source (C:=C) (l:=l)) : ℂ := by
  letI : NeZero (representativeModulus r.left r.right) :=
    ⟨(representativeModulus_pos r.left r.right r.left_supported r.right_supported).ne'⟩
  exact average (fun z : MixedPair (representativeModulus r.left r.right)=>
    primeResidueIndicatorAt r.left r.right r.left_supported r.right_supported
      (r.fixedB x) (z.1,z.2))

theorem mixedBlockAverage_eq_rootValue (r : Frame (l:=l) C outside)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz depth L j))
    (hbulk : ∀u : Slots (depth:=depth) (L:=L) (l:=l),
      bulkSamples C.sources (2*(bulkSize depth L/2)) depth l y u.1 u.2 =
        bulkSamples C.sources (2*(bulkSize depth L/2)) depth l x (σ u).1 (σ u).2)
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (x i).val=(r.leftSource i).val)
    (hfixed' : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (y i).val=(r.rightSource i).val)
    (hg : ((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)
    (hg' : ((r.newRight y).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime) :
    r.mixedBlockAverage σ x y = extractedDensity (C:=C) x * r.rootValue true hV σ x * r.mixedBMean x := by
  have hfix := (assignedSlots_erase_eq C.sources _ x r.leftSource hfixed).symm
  have hfix' := (assignedSlots_erase_eq C.sources _ y r.rightSource hfixed').symm
  have hcop : Nat.Coprime (bulkProduct (assignedSlots C.sources _ x)) outside.prod := by
    apply bulkProduct_coprime_of_static
    simpa only [newLeft,assignedHistory,decodeHistory_root,assignedRoot] using hg
  have hcop' : Nat.Coprime (bulkProduct (assignedSlots C.sources _ y)) outside.prod := by
    apply bulkProduct_coprime_of_static
    simpa only [newRight,assignedHistory,decodeHistory_root,assignedRoot] using hg'
  have heq := HistoryBulkPrincipalRootTest.independent_mixed_source_eq_raw_product_of_mass
    d depth (bulkSize depth L/2) depth l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card)
    (frequencyBound Bs BD Bz depth L) outside
    (assignedRoot C.sources _ r.s r.P.toNat r.Q.toNat r.leftSource)
    (assignedRoot C.sources _ r.t r.P.toNat r.Q.toNat r.rightSource)
    (assignedRoot C.sources _ r.s 1 1 x) (assignedRoot C.sources _ r.t 1 1 y)
    r.leftChoices r.rightChoices σ x y rfl rfl hbulk
    (assignedRoot_matches C.sources _ r.s r.P.toNat r.Q.toNat r.leftSource)
    (assignedRoot_matches C.sources _ r.t r.P.toNat r.Q.toNat r.rightSource)
    rfl rfl hfix hfix' r.left_supported r.right_supported hcop hcop'
    r.outside_primes hV hx hfreq
  have hmul := congrArg (fun z : ℂ=>extractedDensity (C:=C) x*(z*r.mixedBMean x)) heq.symm
  simp only [mixedBlockAverage,rootValue,bulkModulus,frequencyModulus,left,right,
    newLeft,newRight,assignedHistory,mixedBMean,mul_assoc,
    HistoryFrequencyResidues.pairedFrequencyProduct,InitialSourceChoice.sources,
    NominalCenterArray.sources] at hmul ⊢
  exact hmul

theorem masked_mixedBlockAverage_eq_rootValue (r : Frame (l:=l) C outside)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz depth L j))
    (hbulk : ∀u : Slots (depth:=depth) (L:=L) (l:=l),
      bulkSamples C.sources (2*(bulkSize depth L/2)) depth l y u.1 u.2 =
        bulkSamples C.sources (2*(bulkSize depth L/2)) depth l x (σ u).1 (σ u).2)
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (x i).val=(r.leftSource i).val)
    (hfixed' : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (y i).val=(r.rightSource i).val) :
    staticPairMask (r.newLeft x) (r.newRight y) outside * r.mixedBlockAverage σ x y =
      staticPairMask (r.newLeft x) (r.newRight y) outside *
        (extractedDensity (C:=C) x * r.rootValue true hV σ x * r.mixedBMean x) := by
  classical
  by_cases hg : ((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      ((r.newRight y).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime
  · rw [r.mixedBlockAverage_eq_rootValue hV σ x y hx hfreq hbulk hfixed hfixed' hg.1 hg.2]
  · simp only [staticPairMask,guardIndicator,hg,ite_false,zero_mul]

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
