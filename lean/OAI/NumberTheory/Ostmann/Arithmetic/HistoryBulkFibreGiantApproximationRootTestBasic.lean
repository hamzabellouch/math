import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalRootTest

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryPairBulkTransport HistoryBulkProducts
open HistoryBulkDiagramParameters HistoryBulkSpectatorReferenceRaw
open HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry
open HistoryCRTIntegration HistoryBulkResidueNormSum HistoryPrincipalIntegralAverage
open HistoryBulkReferenceTests
open HistorySignedSpectatorCRT HistorySignedResidueFactorization ResidueHaar

theorem bulkProduct_coprime_of_static {xs : List SmallSlot} {outside : List ℕ}
    (h : (xs.map SmallSlot.value ++ outside).Pairwise Nat.Coprime) :
    Nat.Coprime (bulkProduct xs) outside.prod := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro a ha
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  exact (List.pairwise_append.mp h).2.2 q.value
    (List.mem_map.mpr ⟨q,(List.mem_filter.mp hq).1,rfl⟩) p hp

variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
namespace Frame
variable (r : Frame (l:=l) C outside)

def rootValue (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x : Source (C:=C) (l:=l)) : ℂ :=
  rootTest true mixed d r.left r.right r.left_supported r.right_supported
    r.outside_primes hV σ depth
    (sourceBulkUnits (bulkModulus r.left r.right outside depth) C.sources
      (2*(bulkSize depth L/2)) depth l x)

def unitBMean (x : Source (C:=C) (l:=l)) : ℂ := by
  letI : NeZero (representativeModulus r.left r.right) :=
    ⟨(representativeModulus_pos r.left r.right r.left_supported r.right_supported).ne'⟩
  exact average (fun z : UnitPair (representativeModulus r.left r.right)=>
    primeResidueIndicatorAt r.left r.right r.left_supported r.right_supported
      (r.fixedB x) (z.1,z.2))

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
