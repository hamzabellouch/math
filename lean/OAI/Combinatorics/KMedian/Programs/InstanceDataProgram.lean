import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalSelectProgram
import OAI.Combinatorics.KMedian.Programs.UnitGeometryProgram
import OAI.Combinatorics.KMedian.Optimization.FractionalInputProgram
import OAI.Combinatorics.KMedian.Programs.InstanceComputedPseudo

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open RationalUnitInput.Program (ranks pickRows)
abbrev Matrix := List (List ℚ)
abbrev Raw := (Row × Row) × (ℕ × Matrix)
def view (I : Instance) : Raw :=
  ((setView I.clients,setView I.facilities),(I.k,List.ofFn (fun i => List.ofFn (I.distance i))))
abbrev encode (I : Instance) := enc (view I)
def dcData (x : Raw) : Matrix := (pickRows (x.2.2,ranks x.1.1)).map (fun d => pullback (d,ranks x.1.2))
@[fun_prop] theorem dcData_poly : Poly dcData := by unfold dcData; apply list_map <;> fun_prop
 theorem dcData_view (I : Instance) : dcData (view I)=List.ofFn (fun c => List.ofFn (I.indexedDistance c)) := by
  simp only [dcData,view,RationalUnitInput.Program.ranks_view,RationalUnitInput.Program.pickRows_view,
    List.map_ofFn,Function.comp_def,pullback_view]
  rfl
def ddData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.1)
def dfData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.2)
@[fun_prop] theorem ddData_poly : Poly ddData := by unfold ddData; fun_prop
@[fun_prop] theorem dfData_poly : Poly dfData := by unfold dfData; fun_prop
 theorem ddData_view (I : Instance) : ddData (view I)=List.ofFn (fun c => List.ofFn (I.clientDistance c)) := by
  simp only [ddData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
 theorem dfData_view (I : Instance) : dfData (view I)=List.ofFn (fun c => List.ofFn (I.facilityDistance c)) := by
  simp only [dfData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
abbrev Nonzero := {I : Instance // ¬I.zeroTest}
abbrev nzEncode (I : Nonzero) := encode I.val
def lpInput (I : Nonzero) : LPBinary.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,card_pos.mpr I.val.facilities_nonempty,
    card_pos.mpr (I.val.nonzero_clients I.property),I.val.k_pos,I.val.k_le,I.val.indexedDistance⟩
def lpData (x : Raw) : Matrix × ℕ := (dcData x,x.2.1)
@[fun_prop] theorem lpData_poly : Poly lpData := by unfold lpData; fun_prop
noncomputable def lpProgram : PolyProgram nzEncode LPBinary.Input.encode lpInput :=
  lpData_poly.program.recode (fun I => view I.val) (fun _ => rfl) (fun I => congrArg enc (by
    unfold lpData; rw [dcData_view]; rfl))
def fractionalData (x : Raw × LPBinary.Repair.Output) : FractionalRefinement.Program.Raw :=
  (x.2.1,(dcData x.1,(ddData x.1,dfData x.1)))
@[fun_prop] theorem fractionalData_poly : Poly fractionalData := by unfold fractionalData; fun_prop
variable (r : ℕ) (hr : 0<r)
def fractionalInput (I : Nonzero) : FractionalRefinement.Program.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,I.val.computedFractional r hr (I.val.nonzero_clients I.property),
    (I.val.nonzeroFractional_spec I.property r hr).1,card_pos.mpr (I.val.nonzero_clients I.property),
    I.val.indexedDistance,I.val.clientDistance,I.val.facilityDistance,I.val.indexedDistance_nonneg,
    I.val.clientDistance_self,I.val.clientDistance_comm⟩
 theorem fractionalData_view (I : Nonzero) : fractionalData (view I.val,LPBinary.Scale.selected r (lpInput I))=(fractionalInput r hr I).raw := by
  unfold fractionalData
  rw [LPBinary.Scale.selected_eq r hr (lpInput I) I.val.indexedDistance_nonneg,dcData_view,ddData_view,dfData_view]
  rfl
noncomputable def fractionalProgram : PolyProgram nzEncode FractionalRefinement.Program.Input.encode (fractionalInput r hr) :=
  (((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl) |>.fanout
    (lpProgram.comp (LPBinary.Scale.selectedProgram r hr))).comp fractionalData_poly.program).recode
      id (fun _ => rfl) (fun I => congrArg enc (fractionalData_view r hr I))
end MetricKMedian.InstanceProgram
end

end OAI
