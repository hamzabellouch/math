import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalUnitScan
import OAI.Combinatorics.KMedian.Programs.UnitGeometryProgram
import OAI.Combinatorics.KMedian.Preparation.SupplierScanProgram

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
structure Input where
  f : ℕ
  j : ℕ
  m : ℕ
  U : RationalUnitInput f j
  metric : PseudoMetricSpace (Fin m)
  R : @Realization f j U (Fin m) metric
  B : ℚ
abbrev Raw := Program.Raw × ℚ
def Input.raw (x : Input) : Raw := (view x.U,x.B)
abbrev Input.encode (x : Input) := enc x.raw
variable {η τ : ℝ} (p : RationalAllParameters η τ)
def Input.sup (x : Input) : RationalSuppliers.Program.ScanInput :=
  letI := x.metric
  ⟨x.f,(x.U.representatives p.M).card,x.j,x.U.suppliers x.R p,x.U.df,x.U.dc,x.B⟩
def postData (x : Raw × RationalSuppliers.Program.SupplierRaw) : RationalSuppliers.Program.ScanRaw :=
  (x.2,((x.1.1.2.2.2,x.1.1.2.1),x.1.2))
@[fun_prop] theorem postData_poly : Poly postData := by unfold postData; fun_prop
 theorem postData_view (x : Input) :
    postData (x.raw,suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M))))=(x.sup p).raw := by
  let := x.metric
  unfold postData
  rw [suppliersData_view x.U x.R p]
  rfl
def Input.unit (x : Input) : Program.Input := ⟨x.f,x.j,x.U⟩
noncomputable def unitProgram : PolyProgram Input.encode Program.Input.encode Input.unit :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def suppliersProgram : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M)))) :=
  (unitProgram.comp (Program.supplierRawProgram p)).congr _ (fun _ => rfl)
noncomputable def supplierInputProgram : PolyProgram Input.encode RationalSuppliers.Program.ScanInput.encode (Input.sup p) :=
  (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (suppliersProgram p)).comp postData_poly.program).recode
    id (fun _ => rfl) (fun x => congrArg enc (postData_view p x))
def Input.result (x : Input) : Table :=
  letI := x.metric
  ((x.U.scan x.R p x.B).map setView).toList
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (supplierInputProgram p |>.comp (RationalSuppliers.Program.scanProgram p.round)).congr _ (by
    intro x
    simp only [Function.comp_def,Input.result,Input.sup,RationalUnitInput.scan])
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
