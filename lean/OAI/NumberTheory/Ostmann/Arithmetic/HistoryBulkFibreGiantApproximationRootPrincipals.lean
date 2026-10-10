import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryBulkReferencePeriodicMeanSource
open HistoryPrincipalIntegralAverage HistoryGiantPriorGrid
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
namespace Frame
variable (r : Frame (l:=l) C outside)
variable (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
variable (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
variable (x y : Source (C:=C) (l:=l))

def primeRootPrincipal : ℂ := r.giantIntegral x*r.rootValue false hV σ x*r.unitBMean x

def mixedIntegralValue (corrected : Bool) : ℂ :=
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
    (fun _=>logCellMass C.giantCenter ∅)
    (mixedGiantPrimeTest C.giantCenter (if corrected then r.correctedMixedScalar x else r.mixedScalar x))

def mixedRootPrincipal (corrected : Bool) : ℂ :=
  extractedDensity (C:=C) r.leftSource *
    (r.mixedIntegralValue x corrected*r.rootValue true hV σ x*r.mixedBMean x)

theorem masked_mixed_principal_from_block
    (hblock : staticPairMask (r.newLeft x) (r.newRight y) outside*r.mixedBlockAverage σ x y =
      staticPairMask (r.newLeft x) (r.newRight y) outside*
        (extractedDensity (C:=C) x*r.rootValue true hV σ x*r.mixedBMean x))
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (x i).val=(r.leftSource i).val) (corrected : Bool) :
    staticPairMask (r.newLeft x) (r.newRight y) outside*
      (if corrected then r.principalCorrectedMixed σ x y else r.principalMixed σ x y) =
    staticPairMask (r.newLeft x) (r.newRight y) outside*r.mixedRootPrincipal hV σ x corrected := by
  have hd := extractedDensity_eq_of_nonbulk_fixed x r.leftSource hfixed
  have hm : (if corrected then r.principalCorrectedMixed σ x y else r.principalMixed σ x y)=
      r.mixedIntegralValue x corrected*r.mixedBlockAverage σ x y := by
    cases corrected <;> rfl
  rw [hm]
  calc
    _ = r.mixedIntegralValue x corrected*
        (staticPairMask (r.newLeft x) (r.newRight y) outside*r.mixedBlockAverage σ x y) := by ring
    _ = r.mixedIntegralValue x corrected*
        (staticPairMask (r.newLeft x) (r.newRight y) outside*
          (extractedDensity (C:=C) x*r.rootValue true hV σ x*r.mixedBMean x)) :=
      congrArg (fun z:ℂ=>r.mixedIntegralValue x corrected*z) hblock
    _ = _ := by rw [hd]; unfold mixedRootPrincipal; ring

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
