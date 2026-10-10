import Mathlib
import OAI.Combinatorics.KMedian.Preparation.SupplierPreparationProgram
import OAI.Combinatorics.KMedian.Preparation.PreparedScanProgram

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
structure ScanInput where
  f : ℕ
  n : ℕ
  j : ℕ
  S : Data f n
  df : Fin f → Fin f → ℚ
  dc : Fin j → Fin f → ℚ
  budget : ℚ
abbrev ScanRaw := SupplierRaw × ((List (List ℚ) × List (List ℚ)) × ℚ)
def ScanInput.raw (x : ScanInput) : ScanRaw := (supplierView x.S,((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),x.budget))
abbrev ScanInput.encode (x : ScanInput) := enc x.raw
def ScanInput.prep (x : ScanInput) : Input := ⟨x.f,x.n,x.S⟩
def ScanInput.scan (x : ScanInput) : FixedBatch.RationalParameters.PreparedScanProgram.Input :=
  ⟨x.f+x.n*x.f,x.f,x.j,x.df,x.dc,original,x.S.tables qR,x.budget⟩
def originals (x : SupplierRaw) : List ℕ := indices x.1 ++ x.2.2.2.1.flatMap (fun _ => indices x.1)
@[fun_prop] theorem originals_poly : Poly originals := by
  unfold originals
  apply append_poly
  · fun_prop
  · apply list_flatMap <;> fun_prop
 theorem originals_view {f n : ℕ} (S : Data f n) : originals (supplierView S)=List.ofFn (fun i => (original (f:=f) (n:=n) i).val) := by
  rw [show (fun e => (original (f:=f) (n:=n) e).val)=(fun e => Sum.elim (fun i : Fin f => i.val) (fun ti : Fin n × Fin f => ti.2.val) (physicalIndex e)) by
    funext e; unfold original; cases physicalIndex e <;> rfl]
  rw [ofFn_physical]
  simp only [originals,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,List.flatMap_def,List.map_ofFn]
  rw [← List.ofFn_eq_map]
  simp [Function.comp_def]

def scanData (x : ScanRaw × List (List ℕ)) : FixedBatch.RationalParameters.PreparedScanProgram.Raw :=
  ((x.1.1.1.map (fun _ => ()),originals x.1.1),(x.1.2.1,(x.2,x.1.2.2)))
@[fun_prop] theorem scanData_poly : Poly scanData := by
  unfold scanData
  have : Poly (fun x : ScanRaw × List (List ℕ) => x.1.1.1.map (fun _ => ())) := by apply list_map <;> fun_prop
  fun_prop
 theorem scanData_view (x : ScanInput) : scanData (x.raw,(x.S.tables qR).map List.ofFn)=(x.scan qR).raw := by
  unfold scanData ScanInput.raw
  rw [originals_view]
  simp only [supplierView,List.map_ofFn,ScanInput.scan,FixedBatch.RationalParameters.PreparedScanProgram.Input.raw]
  simp only [Function.comp_def,List.ofFn_const]
noncomputable def scanPrepProgram : PolyProgram ScanInput.encode Input.encode ScanInput.prep :=
  (fst enc enc).recode ScanInput.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def scanTablesProgram : PolyProgram ScanInput.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) :=
  (scanPrepProgram.comp (tablesProgram qR)).congr _ (by intro x; simp only [Function.comp_def,ScanInput.prep])
noncomputable def scanRawPairProgram : PolyProgram ScanInput.encode (enc : ScanRaw × List (List ℕ) → List Bool)
    (fun x => (x.raw,(x.S.tables qR).map List.ofFn)) :=
  ((identity enc).recode ScanInput.raw (fun _ => rfl) (fun _ => rfl)).fanout (scanTablesProgram qR)
noncomputable def scanRawProgram : PolyProgram ScanInput.encode enc
    (fun x => scanData (x.raw,(x.S.tables qR).map List.ofFn)) :=
  scanRawPairProgram qR |>.comp scanData_poly.program
noncomputable def scanInputProgram : PolyProgram ScanInput.encode FixedBatch.RationalParameters.PreparedScanProgram.Input.encode (ScanInput.scan qR) :=
  (scanRawProgram qR).recode id (fun _ => rfl) (fun x => congrArg enc (scanData_view qR x))
noncomputable def scanProgram : PolyProgram ScanInput.encode (enc : Table → List Bool)
    (fun x => ((x.S.scan qR x.df x.dc x.budget).map setView).toList) :=
  (scanInputProgram qR |>.comp (FixedBatch.RationalParameters.PreparedScanProgram.program qR)).congr _ (by
    intro x
    simp only [Function.comp_def,FixedBatch.RationalParameters.PreparedScanProgram.Input.result,ScanInput.scan,Data.scan]
    rfl)
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
