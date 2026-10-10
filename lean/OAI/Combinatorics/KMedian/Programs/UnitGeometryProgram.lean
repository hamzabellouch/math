import Mathlib
import OAI.Combinatorics.KMedian.Preparation.SupplierListOperations
import OAI.Combinatorics.KMedian.Programs.BundleGeometryProgram
import OAI.Combinatorics.KMedian.Geometry.RationalAllParameters
import OAI.Combinatorics.KMedian.Geometry.RationalUnitScan
import OAI.Combinatorics.KMedian.Programs.UnitRepresentativeProgram
import OAI.Combinatorics.KMedian.Programs.OriginalMaskProgram

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def pickRows {α : Type} [Inhabited α] (x : List (List α) × List ℕ) : List (List α) :=
  x.2.map (fun i => x.1[i]?.getD [])
@[fun_prop] theorem pickRows_poly {α : Type} [Coding α] [Inhabited α] : Poly (pickRows (α:=α)) := by
  unfold pickRows; apply list_map <;> fun_prop
 theorem pickRows_view {m n k : ℕ} {α : Type} [Inhabited α] (r : Fin k → Fin n) (v : Fin n → Fin m → α) :
    pickRows (List.ofFn (fun i => List.ofFn (v i)),List.ofFn (fun i => (r i).val))=
      List.ofFn (fun i => List.ofFn (v (r i))) := by
  simp only [pickRows,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def geometryData (x : Raw × Row) : RationalBundles.Program.Raw :=
  ((pullbackMatrix (x.1.2.2.1,ranks x.2),pickRows (x.1.2.1,ranks x.2)),
    (pickRows (x.1.1.2,ranks x.2),x.1.1.1))
@[fun_prop] theorem geometryData_poly : Poly geometryData := by unfold geometryData; fun_prop
 theorem geometryData_view {f j : ℕ} (U : RationalUnitInput f j) (M : ℚ) :
    geometryData (view U,setView (U.representatives M))=
      RationalBundles.Program.view (fun t u => U.dd (U.ridx M t) (U.ridx M u))
        (fun t a => U.dc (U.ridx M t) a) (fun t => U.F (U.ridx M t)) U.y := by
  unfold geometryData
  rw [ranks_view]
  simp only [view,ridx,pullbackMatrix_view,pickRows_view,setView,RationalBundles.Program.view]
  rfl

noncomputable def geometryProgram (M : ℚ) : PolyProgram Input.encode enc
    (fun x => geometryData (x.raw,setView (x.U.representatives M))) :=
  ((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (repProgram M)).comp geometryData_poly.program

def suppliersData (δ γ : ℚ) (x : RationalBundles.Program.Raw) : RationalSuppliers.Program.SupplierRaw :=
  (x.2.2,(RationalBundles.Program.bundlesData δ x,(RationalBundles.Program.missingData δ x,
    (RationalBundles.Program.massData (x.2.2,RationalBundles.Program.bundlesData δ x),
      (RationalBundles.Program.massData (x.2.2,RationalBundles.Program.missingData δ x),γ)))))
@[fun_prop] theorem suppliersData_poly (δ γ : ℚ) : Poly (suppliersData δ γ) := by unfold suppliersData; fun_prop
 theorem suppliersData_view {f j : ℕ} (U : RationalUnitInput f j) {X : Type} [PseudoMetricSpace X]
    (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ) :
    suppliersData p.δ p.γ (geometryData (view U,setView (U.representatives p.M)))=
      RationalSuppliers.Program.supplierView (U.suppliers R p) := by
  rw [geometryData_view]
  unfold suppliersData
  rw [RationalBundles.Program.bundlesData_view,RationalBundles.Program.missingData_view]
  simp only [RationalBundles.Program.view,RationalBundles.Program.massData_view]
  rfl

noncomputable def supplierRawProgram {η τ : ℝ} (p : RationalAllParameters η τ) : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (x.raw,setView (x.U.representatives p.M)))) :=
  geometryProgram p.M |>.comp (suppliersData_poly p.δ p.γ).program
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
