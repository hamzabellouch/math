import Mathlib
import OAI.Combinatorics.KMedian.Process.CountsMaskProgram
import OAI.Combinatorics.KMedian.Rounding.GridDataProgram

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList
variable {τ : ℝ} (q : RationalParameters τ)
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  n : Fin f → ℕ
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × List ℕ)
def Input.raw (x : Input) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),List.ofFn x.n))
abbrev Input.encode (x : Input) := enc x.raw

def cap (Δ : ℕ) (ns : List ℕ) : Bool := (ns.map (fun n => decide (n≤Δ))).all id
@[fun_prop] theorem cap_poly (Δ : ℕ) : Poly (cap Δ) := by unfold cap; apply comp bool_all; apply list_map <;> fun_prop
 theorem cap_input (x : Input) : cap q.Δ (List.ofFn x.n)=decide (∀ i, x.n i≤q.Δ) := by
  apply Bool.eq_iff_iff.mpr
  simp [cap]

def valid (Δ : ℕ) (x : Raw) : Bool := cap Δ x.2.2 && decide (Δ≤Completion.Rational.BestProgram.card (CopyState.CountsProgram.mask Δ x.2.2))
@[fun_prop] theorem valid_poly (Δ : ℕ) : Poly (valid Δ) := by unfold valid; fun_prop
 theorem valid_input (x : Input) (hn : ∀ i, x.n i≤q.Δ) : valid q.Δ x.raw=decide (q.Δ≤(CopyState.activeSlots x.n hn).card) := by
  unfold valid Input.raw
  dsimp only
  rw [cap_input q x,decide_eq_true hn,Bool.true_and,CopyState.CountsProgram.mask_view x.n hn,
    CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

def dummy : SelectionProgram.Input q where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c
  d₀ := fun i => Fin.elim0 i

def Input.selection (x : Input) : SelectionProgram.Input q :=
  if hn : ∀ i, x.n i≤q.Δ then
    if hA : q.Δ≤(CopyState.activeSlots x.n hn).card then
      GridDataProgram.Input.selection q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩
    else dummy q
  else dummy q

def prepare (x : Raw) : SelectionProgram.Raw :=
  if valid q.Δ x then GridDataProgram.prepare q.Δ (x.1,(x.2.1,CopyState.CountsProgram.mask q.Δ x.2.2))
  else (dummy q).raw
@[fun_prop] theorem prepare_poly : Poly (prepare q) := by unfold prepare; fun_prop
 theorem prepare_input (x : Input) : prepare q x.raw=(x.selection q).raw := by
  unfold prepare Input.selection
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · rw [dite_eq_left hA,ite_eq_left (decide_eq_true hA)]
      rw [show (x.raw.1,(x.raw.2.1,CopyState.CountsProgram.mask q.Δ x.raw.2.2))=
        GridDataProgram.Input.raw q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩ by
          unfold Input.raw GridDataProgram.Input.raw
          dsimp only
          rw [CopyState.CountsProgram.mask_view x.n hn]]
      exact GridDataProgram.prepare_input q _
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false]

def Input.result (x : Input) : Table := ((q.roundCounts x.d₀ x.d x.n).map setView).toList

def finish (x : Raw × Table) : Table := if valid q.Δ x.1 then x.2 else []
@[fun_prop] theorem finish_poly : Poly (finish q) := by unfold finish; fun_prop
 theorem finish_input (x : Input) : finish q (x.raw,SelectionProgram.Input.result q (x.selection q))=x.result q := by
  unfold finish Input.result RationalParameters.roundCounts
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · simp only [dite_eq_left hA,decide_eq_true hA,ite_true,Input.selection,dite_eq_left hn]
      rfl
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]

noncomputable def program : PolyProgram Input.encode SparseGraph.ListOperation.et (Input.result q) := by
  let p : PolyProgram Input.encode (SelectionProgram.Input.encode q) (fun x => x.selection q) :=
    (prepare_poly q).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input q x))
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (r.fanout (p.comp (SelectionProgram.program q)) |>.comp (finish_poly q).program).congr _ (finish_input q)
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
