import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawLeaves
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseOutside
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSpectator

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction HistoryBulkProducts HistoryBulkSupportConverse HistoryBulkFrequencyTransport
open HistoryResidueRegular HistorySignedSpectatorDiagram HistorySignedSpectatorCRT HistorySignedResidues
open HistoryBulkSpectatorDiagramAverage HistoryBulkSpectatorProduct HistorySignedSpectatorDiagramAverage
open HistoryOccurrenceVariables HistoryCRTIntegration CanonicalHistoryLeafBulk

theorem residuePair_eq_projected_product_static {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i:InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (ku : ∀i:InternalKey k,Nat.Coprime (internalSlot k i).value outside.prod)
    (g : (q:ℕ)→ZMod q→ℂ) (z : ZMod outside.prod×ZMod outside.prod) :
    residuePairSpectator g outside outside.prod h k z=
      ∏i:Fin outside.length,primePair h k g outside (primeAt outside i)
        (projectedRingPair (List.dvd_prod (List.get_mem outside i)) z) := by
  have hh := (divisorData_of_static h hs).mono (dvd_mul_right (divisorProduct h) (divisorProduct k))
  have hk := (divisorData_of_static k ks).mono (dvd_mul_left (divisorProduct k) (divisorProduct h))
  have hc : Nat.Coprime (divisorProduct h*divisorProduct k).natAbs outside.prod := by
    rw [Int.natAbs_mul]
    exact (divisorProduct_coprime_of_frequencies_internal h outside.prod
      (static_frequencies_coprime_outside h hs outside hp hV) hu).mul_left
      (divisorProduct_coprime_of_frequencies_internal k outside.prod
        (static_frequencies_coprime_outside k ks outside hp hV) ku)
  rw [residuePairSpectator_eq_primeProduct h k g outside _ outside.prod
    (fun q hq=>List.dvd_prod hq) hh hk hc]
  symm
  simpa only [primePair,primeAt,List.get_eq_getElem,projectedRingPair,ZMod.castHom_apply] using
    Fin.prod_univ_fun_getElem outside (fun q=>primePair h k g outside q (ZMod.cast z.1,ZMod.cast z.2))

theorem unitTest_eq_raw_of_leaves {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k h' k' : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hn : StaticSkeleton V h') (kn : StaticSkeleton V k')
    (hf : SameFrequencyData h h') (kf : SameFrequencyData k k')
    (hfix : fixedProduct h.root.small=fixedProduct h'.root.small)
    (kfix : fixedProduct k.root.small=fixedProduct k'.root.small)
    (hc : Nat.Coprime (bulkProduct h'.root.small) outside.prod)
    (kc : Nat.Coprime (bulkProduct k'.root.small) outside.prod)
    (hu : ∀i:InternalKey h',Nat.Coprime (internalSlot h' i).value outside.prod)
    (ku : ∀i:InternalKey k',Nat.Coprime (internalSlot k' i).value outside.prod)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) (roots : UnitPair outside.prod)
    (samples : Fin (2^l)×Fin m→(ZMod outside.prod)ˣ)
    (hleaves : ∀q (hq:q∈outside),
      orderedProducts σ (fun u=>ZMod.unitsMap (List.dvd_prod hq) (samples u))=
        (rawLeaves q h',rawLeaves q k')) :
    unitTest h k hs ks hp hV σ g roots samples=
      residuePairSpectator g outside outside.prod h' k' (roots.1,roots.2) := by
  rw [residuePair_eq_projected_product_static h' k' hn kn hp hV hu ku]
  unfold unitTest
  let := primeAtFact hp
  apply Finset.prod_congr rfl
  intro i _
  let q := primeAt outside i
  have hq : q∈outside := List.get_mem outside i
  dsimp only [localUnitTest,unitProjection,orderedIntegrand]
  rw [hleaves q hq]
  rw [bulkDiagram_value_raw h h' hs (supported_regular h hs hq (hV q hq)) hn hf hfix
      (hc.of_dvd_right (List.dvd_prod hq)) _ _ _ _ (hg q hq),
    bulkDiagram_value_raw k k' ks (supported_regular k ks hq (hV q hq)) kn kf kfix
      (kc.of_dvd_right (List.dvd_prod hq)) _ _ _ _ (hg q hq)]
  rfl

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
