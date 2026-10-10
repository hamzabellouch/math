import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliRunProgram
import OAI.Combinatorics.KMedian.Process.PhysicalBatchList
import OAI.Combinatorics.KMedian.Sparse.SparseMixProgram

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse SparseIntegerLaw.DependentProgram
open SparseGraph.ListOperation (Row Table et)
local notation "br" => SparseGraph.ListOperation.er

structure Input where
  n : ℕ
  Z : Finset (Fin n)
  C : Fin n → Finset (Fin n)
  p : ℚ
  q : Fin n → ℚ
  hp : 0≤p ∧ p≤1
  hq : ∀ e, 0≤q e ∧ q e≤1

def Input.raw (x : Input) : ListOperation.Raw :=
  ((SparseGraph.ListOperation.setView x.Z,List.ofFn fun e => SparseGraph.ListOperation.setView (x.C e)),
    (x.p,List.ofFn x.q))
abbrev Input.encode (x : Input) := Binary.Automatic.enc x.raw

def Input.bernInput (bal : Bool) (x : Input) : SparseBernoulli.Program.Input :=
  ⟨x.n,(fun i => if bal then x.p else x.q i),fun i => by cases bal <;> [exact x.hq i; exact x.hp]⟩
def Input.bern (bal : Bool) (x : Input) : SparseIntegerLaw (Fin x.n → Bool) :=
  SparseBernoulli.run (d:=4) (x.bernInput bal).p (x.bernInput bal).feasible x.n
def Input.part (bal : Bool) (x : Input) : SparseIntegerLaw (Finset (Fin x.n)) :=
  (x.bern bal).map (fun ω => if bal then balanced x.Z x.C ω else unbalanced x.Z ω)
def Input.partData (bal : Bool) (x : Input) : Data Row :=
  (((x.part bal).law.denominator,List.ofFn (x.part bal).law.numerator),
    (x.part bal).states.toList.map SparseGraph.ListOperation.setView)
def Input.result (x : Input) : Data Row :=
  (((law x.Z x.C x.p x.q x.hp x.hq).law.denominator,List.ofFn (law x.Z x.C x.p x.q x.hp x.hq).law.numerator),
    (law x.Z x.C x.p x.q x.hp x.hq).states.toList.map SparseGraph.ListOperation.setView)

noncomputable def bernInputProgram (bal : Bool) :
    PolyProgram Input.encode SparseBernoulli.Program.Input.encode (Input.bernInput bal) := by
  let raw : PolyProgram Binary.Automatic.enc SparseBernoulli.Program.qr
      (fun x : ListOperation.Raw => if bal then x.2.2.map (fun _ => x.2.1) else x.2.2) := by
    apply Binary.Automatic.Poly.program
    have hm : Binary.Automatic.Poly (fun x : ListOperation.Raw => x.2.2.map (fun _ => x.2.1)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    cases bal <;> simp only [Bool.false_eq_true,ite_false,ite_true,Input.raw,List.map_const',List.length_ofFn,
      Input.bernInput,SparseBernoulli.Program.Input.encode,List.ofFn_const,Fin.cast_eq_self])

noncomputable def bernProgram (bal : Bool) : PolyProgram Input.encode (ed br)
    (fun x : Input => (((x.bern bal).law.denominator,List.ofFn (x.bern bal).law.numerator),
      (x.bern bal).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed br)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed br)).recode
      (Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernInputProgram bal |>.comp (SparseBernoulli.Program.runStateProgram 4) |>.comp get).congr _ (fun _ => rfl)

noncomputable def partProgram (bal : Bool) : PolyProgram Input.encode (ed br) (Input.partData bal) := by
  let ctx : PolyProgram Input.encode Binary.Automatic.enc Input.raw := (identity Binary.Automatic.enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let post : PolyProgram (encodePair Binary.Automatic.enc (ed br)) (ed br)
      (fun x : ListOperation.Raw × Data Row => (x.2.1,x.2.2.map (fun row => ListOperation.select bal (x.1,row)))) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (ctx.fanout (bernProgram bal) |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.partData,Input.part,SparseIntegerLaw.map,Vector.toList_map,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro ω hω
    exact ListOperation.select_view x.Z x.C x.p x.q ω bal)

noncomputable def program : PolyProgram Input.encode (ed br) Input.result :=
  ((partProgram true).fanout (partProgram false) |>.comp mixData_poly.program).congr _ (fun x => by
    change mixData (((raw (x.part true)).1,(x.part true).states.toList.map SparseGraph.ListOperation.setView),
      ((raw (x.part false)).1,(x.part false).states.toList.map SparseGraph.ListOperation.setView))=_
    rw [mixData_raw]
    rfl)
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
