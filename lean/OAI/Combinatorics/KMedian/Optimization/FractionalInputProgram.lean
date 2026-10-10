import Mathlib
import OAI.Combinatorics.KMedian.Programs.UnitRepresentativeProgram
import OAI.Combinatorics.KMedian.Programs.NearestListProgram
import OAI.Combinatorics.KMedian.Programs.OriginalMaskProgram
import OAI.Combinatorics.KMedian.Programs.SplitListProgram
import OAI.Combinatorics.KMedian.Geometry.RationalFractionalInput

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Matrix := List (List ℚ)
abbrev Raw := List ℚ × (Matrix × (Matrix × Matrix))
structure Input where
  f : ℕ
  j : ℕ
  k : ℕ
  a : TruncatedLP.FractionalData f j
  ha : a.Valid k
  hj : 0<j
  dc : Fin j → Fin f → ℚ
  dd : Fin j → Fin j → ℚ
  df : Fin f → Fin f → ℚ
  hdc : ∀ c i, 0≤dc c i
  hdd : ∀ c, dd c c=0
  hds : ∀ c c', dd c c'=dd c' c
abbrev Input.raw (z : Input) : Raw :=
  (List.ofFn (y z.a),(List.ofFn (fun c => List.ofFn (z.dc c)),
    (List.ofFn (fun c => List.ofFn (z.dd c)),List.ofFn (fun a => List.ofFn (z.df a)))))
abbrev Input.encode (z : Input) := enc z.raw

def assignmentData (z : Raw) : Matrix := z.2.1.map (fun d => LPBinary.Nearest.filling z.1 d)
@[fun_prop] theorem assignmentData_poly : Poly assignmentData := by
  have h : Poly (fun z : Raw => (z.1,z.2.1)) := by fun_prop
  exact ⟨(h.program.comp (LPBinary.Nearest.fillingProgram.listMapWith [] [])).congr _ (fun _ => rfl)⟩
 theorem assignmentData_view (z : Input) : assignmentData z.raw=List.ofFn (fun c => List.ofFn (x z.a z.k z.ha z.hj z.dc c)) := by
  simp only [assignmentData,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext c
  exact LPBinary.Nearest.filling_ofFn _ _ (fun i => (z.ha.1 i).1) (mass_one z.a z.k z.ha z.hj)

def splitData (z : Raw) : RationalSplitting.Program.Raw := (z.1,assignmentData z)
@[fun_prop] theorem splitData_poly : Poly splitData := by unfold splitData; fun_prop
 theorem splitData_view (z : Input) : splitData z.raw=RationalSplitting.Program.view (y z.a) (x z.a z.k z.ha z.hj z.dc) := by
  unfold splitData
  rw [assignmentData_view]
  rfl

def unitData (z : Raw) : RationalUnitInput.Program.Raw :=
  ((RationalSplitting.Program.weightsData (splitData z),RationalSplitting.Program.assignedData (splitData z)),
    (z.2.1.map (fun d => pullback (d,RationalSplitting.Program.originalData (splitData z))),
      (z.2.2.1,pullbackMatrix (z.2.2.2,RationalSplitting.Program.originalData (splitData z)))))
@[fun_prop] theorem unitData_poly : Poly unitData := by
  unfold unitData
  have h : Poly (fun z : Raw => z.2.1.map (fun d => pullback (d,RationalSplitting.Program.originalData (splitData z)))) := by
    apply list_map <;> fun_prop
  fun_prop

def Input.unit (z : Input) : RationalUnitInput.Program.Input :=
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,unitInput z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds⟩
 theorem unitData_view (z : Input) : unitData z.raw=z.unit.raw := by
  unfold unitData
  rw [splitData_view,RationalSplitting.Program.weightsData_view,RationalSplitting.Program.assignedData_view,
    RationalSplitting.Program.originalData_view]
  simp only [List.map_ofFn,Function.comp_def,pullback_view,pullbackMatrix_view]
  rfl
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.Program.Input.encode Input.unit :=
  unitData_poly.program.recode Input.raw (fun _ => rfl) (fun z => congrArg enc (unitData_view z))
noncomputable def originalProgram : PolyProgram Input.encode (enc : List ℕ → List Bool)
    (fun z => List.ofFn (fun b => (original z.a z.k z.ha z.hj z.dc b).val)) :=
  ((Poly.comp RationalSplitting.Program.originalData_poly splitData_poly).program.recode Input.raw (fun _ => rfl)
    (fun z => congrArg enc (by rw [splitData_view,RationalSplitting.Program.originalData_view]; rfl)))
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
