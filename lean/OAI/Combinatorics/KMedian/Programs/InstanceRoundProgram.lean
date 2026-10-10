import Mathlib
import OAI.Combinatorics.KMedian.Optimization.IndexedInstanceLP
import OAI.Combinatorics.KMedian.Programs.InstanceComputedPseudo
import OAI.Combinatorics.KMedian.Binary.BinaryGuardTotal
import OAI.Combinatorics.KMedian.Programs.InstanceZeroProgram
import OAI.Combinatorics.KMedian.Optimization.FractionalScanProgram

namespace OAI


                                            
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
variable (r : ℕ) (hr : 0<r) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ)
def scanInput (I : Nonzero) : FractionalRefinement.ScanProgram.Input :=
  { fractionalInput r hr I with
    m := I.val.n
    metric := I.val.pseudoMetric
    facility := I.val.facilities.orderEmbOfFin rfl
    client := I.val.clients.orderEmbOfFin rfl
    hdf := fun _ _ => rfl
    hc := fun _ _ => rfl
    hcc := fun _ _ => rfl
    B := I.val.k+C }
noncomputable def budgetProgram : PolyProgram nzEncode (enc : ℚ → List Bool) (fun I => (I.val.k:ℚ)+C) :=
  (by fun_prop : Poly (fun x : Raw => (x.2.1:ℚ)+C)).program.recode (fun I => view I.val) (fun _ => rfl) (fun _ => rfl)
noncomputable def scanInputProgram : PolyProgram nzEncode FractionalRefinement.ScanProgram.Input.encode (scanInput r hr C) :=
  ((fractionalProgram r hr).fanout (budgetProgram C)).recode id (fun _ => rfl) (fun _ => rfl)
def imageData (x : Raw × Table) : Table := x.2.map (fun row => imageRaw
  ((x.1.1.2.map (fun _ => ()),RationalUnitInput.Program.ranks x.1.1.2),row))
@[fun_prop] theorem imageData_poly : Poly imageData := by unfold imageData; apply list_map <;> fun_prop
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
 theorem imageData_view (I : Nonzero) :
    imageData (view I.val,(scanInput r hr C I).result p)=((I.val.nonzeroRound I.property r hr p C).map setView).toList := by
  let := I.val.pseudoMetric
  unfold imageData
  simp only [view]
  rw [RationalUnitInput.Program.ranks_view]
  simp only [setView,List.map_ofFn,Function.comp_def,List.ofFn_const]
  convert FractionalRefinement.ScanProgram.imageRaw_option (I.val.facilities.orderEmbOfFin rfl)
    (FractionalRefinement.scan (I.val.computedFractional r hr (I.val.nonzero_clients I.property)) I.val.k
      (I.val.nonzeroFractional_spec I.property r hr).1 (card_pos.mpr (I.val.nonzero_clients I.property))
      I.val.indexedDistance I.val.clientDistance I.val.facilityDistance
      I.val.indexedDistance_nonneg I.val.clientDistance_self I.val.clientDistance_comm
      (I.val.facilities.orderEmbOfFin rfl) (I.val.clients.orderEmbOfFin rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p (I.val.k+C)) using 1
  unfold FractionalRefinement.ScanProgram.Input.result
  rfl
  rfl
noncomputable def nonzeroRoundProgram : PolyProgram nzEncode (enc : Table → List Bool)
    (fun I => ((I.val.nonzeroRound I.property r hr p C).map setView).toList) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    ((scanInputProgram r hr C).comp (FractionalRefinement.ScanProgram.program p))).comp imageData_poly.program).congr
      _ (imageData_view r hr p C)

def fallbackData (x : Raw × Table) : Row := if x.2.isEmpty then singletonData x.1 else x.2.head?.getD []
@[fun_prop] theorem fallbackData_poly : Poly fallbackData := by unfold fallbackData; fun_prop
noncomputable def nonzeroPseudoProgram : PolyProgram nzEncode (enc : Row → List Bool)
    (fun I => setView ((I.val.nonzeroRound I.property r hr p C).getD {I.val.facilities.min' I.val.facilities_nonempty})) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    (nonzeroRoundProgram r hr p C)).comp fallbackData_poly.program).congr _ (by
      intro I
      simp only [Function.comp_def,fallbackData,id_eq,singletonData_view]
      cases I.val.nonzeroRound I.property r hr p C <;> rfl)
noncomputable def pseudoProgram : PolyProgram encode (enc : Row → List Bool)
    (fun I => setView (I.computedPseudo r hr p C)) :=
  (dependentIfTotal Instance.zeroTest zeroTestProgram
    (fun I h => setView ((I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}))
    (fun I _ => setView I.zeroOutput) (nonzeroPseudoProgram r hr p C)
    (zeroOutputProgram.recode Subtype.val (fun _ => rfl) (fun _ => rfl))).congr _ (by
      intro I
      unfold Instance.computedPseudo
      split_ifs <;> rfl)
end MetricKMedian.InstanceProgram
end

end OAI
