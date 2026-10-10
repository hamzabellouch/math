import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalHistoriesProgram
import OAI.Combinatorics.KMedian.Geometry.RationalHistoryCompletion
import OAI.Combinatorics.KMedian.Geometry.RationalHistorySelection
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters
import OAI.Combinatorics.KMedian.Programs.MaskBestProgram
import OAI.Combinatorics.KMedian.Reduction.CompletionProgram

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

structure Input extends Completion.Rational.Program.Input q.Δ where
  d₀ : Fin f → Fin f → ℚ
abbrev Raw := List (List ℚ) × Completion.Rational.Program.Raw
def Input.raw (x : Input q) : Raw := (List.ofFn (fun i => List.ofFn (x.d₀ i)),x.toInput.raw)
abbrev Input.encode (x : Input q) := enc x.raw

def Input.ctx (x : Input q) : UpdateProgram.Context where
  f := x.f
  Δ := q.Δ
  d := x.d₀
  g := q.g
  P := 1
  positive := by norm_num
  A := x.A
  β := q.β
  p := q.probabilityQ
  φ := q.φ
  hp := q.probabilityQ_pos.le
  hφ := by exact_mod_cast q.φpos.le
  hupper := q.probabilityQ_le

def ctxRaw (x : Raw) : RoundProgram.Raw := (((((q.g,1),q.Δ),x.1),x.2.2.2.2),(q.β,(q.probabilityQ,q.φ)))
@[fun_prop] theorem ctxRaw_poly : Poly (ctxRaw q) := by unfold ctxRaw; fun_prop
 theorem ctxRaw_input (x : Input q) : ctxRaw q x.raw=RoundProgram.ctxRaw (x.ctx) := rfl
noncomputable def historyProgram : PolyProgram (Input.encode q) (ed SparseGraph.ListOperation.er)
    (fun x => HistoryProgram.result q.taperAt q.T x.ctx) := by
  let c : PolyProgram (Input.encode q) RoundProgram.ctxEncode (Input.ctx q) :=
    (ctxRaw_poly q).program.recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  exact c.comp (HistoryProgram.program q.taperAt q.T (fun t _ => by exact_mod_cast q.taperAt_pos t))

def Input.items (x : Input q) : List (Completion.Rational.Program.Input q.Δ) :=
  (q.tree x.d₀ x.A).states.toList.map (fun z => {x.toInput with A:=z.1.1})
def attach (x : Raw × Data Row) : List Completion.Rational.Program.Raw :=
  x.2.2.map (fun A => (x.1.2.1,(x.1.2.2.1,(x.1.2.2.2.1,A))))
@[fun_prop] theorem attach_poly : Poly attach := by unfold attach; apply list_map <;> fun_prop
 theorem attach_input (x : Input q) : attach (x.raw,HistoryProgram.result q.taperAt q.T x.ctx)=
    x.items.map Completion.Rational.Program.Input.raw := by
  simp only [attach,HistoryProgram.result,table,Input.items,List.map_map,Function.comp_def]
  rfl
noncomputable def itemsProgram : PolyProgram (Input.encode q) (encodeList Completion.Rational.Program.Input.encode) (Input.items q) := by
  let raw : PolyProgram (Input.encode q) enc (Input.raw q) := (identity enc).recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  exact (raw.fanout (historyProgram q) |>.comp attach_poly.program).recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_def,id_eq]
    rw [attach_input q]
    change encodeList enc _=encodeList Completion.Rational.Program.Input.encode _
    rw [encodeList_map]
    rfl)

def dummy : Completion.Rational.Program.Input q.Δ where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c

def metadata (x : Raw) : ℚ × List (List ℚ) :=
  (q.g*Completion.Rational.BestProgram.card x.2.2.2.2+q.allowance,x.2.2.1.1)
@[fun_prop] theorem metadata_poly : Poly (metadata q) := by unfold metadata; fun_prop
 theorem metadata_input (x : Input q) : metadata q x.raw=(q.g*x.A.card+q.allowance,List.ofFn (fun c => List.ofFn (x.d c))) := by
  unfold metadata Input.raw Completion.Rational.Program.Input.raw
  dsimp only
  rw [CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

def Input.result (x : Input q) : Table :=
  ((q.selectCompleted x.d₀ x.d x.R x.A x.B x.hB).map setView).toList
noncomputable def program : PolyProgram (Input.encode q) SparseGraph.ListOperation.et (Input.result q) := by
  let m := (metadata_poly q).program.recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  let complete := (itemsProgram q).comp ((Completion.Rational.Program.program q.Δ).listMap (dummy q))
  exact (m.fanout complete |>.comp Completion.Rational.BestProgram.raw_poly.program).congr _ (fun x => by
    change Completion.Rational.BestProgram.raw
      (metadata q x.raw,x.items.map (fun y => setView (Completion.Rational.output y.d y.R y.A y.B y.hB)))=x.result
    rw [metadata_input q]
    simp only [Input.items,List.map_map,Function.comp_def]
    rw [show (fun z => setView (Completion.Rational.output x.d x.R z.1.1 x.B x.hB))=
      setView ∘ (fun z => RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β z) from rfl]
    rw [← List.map_map,Completion.Rational.BestProgram.raw_best]
    rw [← SparseSelect.best_map (q.completedGood x.d x.R x.A x.B x.hB)
      (fun z => Completion.Rational.score x.d (RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β z))
      (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤q.g*x.A.card+q.allowance))
      (Completion.Rational.score x.d) (RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β)
      (fun _ => rfl) (fun _ => rfl)]
    rfl)
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
