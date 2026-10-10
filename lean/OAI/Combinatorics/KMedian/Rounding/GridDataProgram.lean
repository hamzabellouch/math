import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyNearestProgram
import OAI.Combinatorics.KMedian.Programs.HistorySelectionProgram

namespace OAI


                                       
section
namespace MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList CopyNearestProgram
variable {τ : ℝ} (q : RationalParameters τ)
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  A : Finset (CopyState.Copy (F:=Fin f) q.Δ)
  enough : q.Δ≤A.card
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × Row)
def Input.raw (x : Input q) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),view x.A))
abbrev Input.encode (x : Input q) := enc x.raw

def Input.selection (x : Input q) : SelectionProgram.Input q where
  f := x.f
  j := x.j
  d := x.d
  R := q.radius x.d x.A x.enough
  A := x.A
  B := q.nearest x.d x.A
  hB := q.nearest_nonempty x.d x.A x.enough
  d₀ := x.d₀

def prepare (Δ : ℕ) (x : Raw) : SelectionProgram.Raw :=
  (x.2.1.1,(x.1,((x.2.1.2,x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))),
    (x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2)),x.2.2))))
@[fun_prop] theorem prepare_poly (Δ : ℕ) : Poly (prepare Δ) := by
  unfold prepare
  have hr : Poly (fun x : Raw => x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  have hn : Poly (fun x : Raw => x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  fun_prop
 theorem prepare_input (x : Input q) : prepare q.Δ x.raw=x.selection.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,nearestRaw_view q,radiusRaw_view q x.d x.A x.enough]
  rfl
noncomputable def program : PolyProgram (Input.encode q) SparseGraph.ListOperation.et
    (fun x => SelectionProgram.Input.result q x.selection) := by
  let p : PolyProgram (Input.encode q) (SelectionProgram.Input.encode q) (Input.selection q) :=
    (prepare_poly q.Δ).program.recode (Input.raw q) (fun _ => rfl) (fun x => congrArg enc (prepare_input q x))
  exact p.comp (SelectionProgram.program q)
end MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
end

end OAI
