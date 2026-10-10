import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalInputProgram
import OAI.Combinatorics.KMedian.Geometry.RationalFractionalScan
import OAI.Combinatorics.KMedian.Programs.UnitScanProgram

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
structure Input extends Program.Input where
  m : ℕ
  metric : PseudoMetricSpace (Fin m)
  facility : Fin f → Fin m
  client : Fin j → Fin m
  hdf : ∀ b b', @dist _ metric.toDist (facility b) (facility b')=(df b b':ℝ)
  hc : ∀ c b, @dist _ metric.toDist (client c) (facility b)=(dc c b:ℝ)
  hcc : ∀ c c', @dist _ metric.toDist (client c) (client c')=(dd c c':ℝ)
  B : ℚ
abbrev Raw := Program.Raw × ℚ
def Input.raw (z : Input) : Raw := (z.toInput.raw,z.B)
abbrev Input.encode (z : Input) := enc z.raw

def Input.unit (z : Input) : RationalUnitInput.ScanProgram.Input :=
  letI := z.metric
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,z.m,z.toInput.unit.U,z.metric,
    realization z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc,z.B⟩
noncomputable def baseProgram : PolyProgram Input.encode Program.Input.encode Input.toInput :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def budgetProgram : PolyProgram Input.encode enc Input.B :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.ScanProgram.Input.encode Input.unit :=
  ((baseProgram.comp Program.unitProgram).fanout budgetProgram).recode id (fun _ => rfl) (fun _ => rfl)
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
variable {η τ : ℝ} (p : RationalAllParameters η τ)
noncomputable def masksProgram : PolyProgram Input.encode (enc : Table → List Bool)
    (fun z => RationalUnitInput.ScanProgram.Input.result p z.unit) :=
  @PolyProgram.comp Input RationalUnitInput.ScanProgram.Input Table Input.encode
    RationalUnitInput.ScanProgram.Input.encode enc Input.unit (RationalUnitInput.ScanProgram.Input.result p)
    unitProgram (RationalUnitInput.ScanProgram.program p)
def imageData (x : Program.Raw × Table) : Table := x.2.map (fun row => imageRaw
  ((x.1.1.map (fun _ => ()),RationalSplitting.Program.originalData (Program.splitData x.1)),row))
@[fun_prop] theorem imageData_poly : Poly imageData := by
  unfold imageData
  have h : Poly (fun x : (Program.Raw × Table) × Row => x.1.1.1.map (fun _ => ())) := by apply list_map <;> fun_prop
  apply list_map
  · fun_prop
  · fun_prop
def Input.result (z : Input) : Table :=
  letI := z.metric
  ((scan z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc p z.B).map setView).toList
 theorem imageRaw_option {f n : ℕ} (g : Fin n → Fin f) (O : Option (Finset (Fin n))) :
    (O.map setView).toList.map (fun row => imageRaw ((List.replicate f (),List.ofFn (fun b => (g b).val)),row))=
    ((O.map (fun S => S.image g)).map setView).toList := by
  cases O with
  | none => rfl
  | some S => simp only [Option.map_some,Option.toList_some,List.map_cons,List.map_nil,imageRaw_view]
 theorem imageData_view (z : Input) : imageData (z.toInput.raw,RationalUnitInput.ScanProgram.Input.result p z.unit)=z.result p := by
  let := z.metric
  unfold imageData
  rw [Program.splitData_view,RationalSplitting.Program.originalData_view]
  have hu : z.toInput.raw.1.map (fun _ => ())=List.replicate z.f () := by
    simp only [List.map_ofFn,Function.comp_def,List.ofFn_const]
  rw [hu]
  simp only [RationalUnitInput.ScanProgram.Input.result,Input.unit,Program.Input.unit]
  simp only [Input.result,scan]
  convert (imageRaw_option (original z.a z.k z.ha z.hj z.dc)
      ((unitInput z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds).scan
        (realization z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc) p z.B)) using 1
  rfl
attribute [irreducible] Input.result
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (PolyProgram.comp (g:=imageData)
    (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.comp (fst enc enc)).fanout (masksProgram p))
    imageData_poly.program).congr _ (imageData_view p)
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
