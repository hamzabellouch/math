import Mathlib
import OAI.Combinatorics.KMedian.Programs.DependentSparseProgram
import OAI.Combinatorics.KMedian.Sparse.SparseProductProgram
import OAI.Combinatorics.KMedian.Process.CountListOperations

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)
abbrev InputRaw := List Unit × List (Data Row)
abbrev ei : InputRaw → List Bool := Binary.Automatic.enc

structure Input where
  n : ℕ
  m : ℕ
  columns : Fin m → SparseIntegerLaw ((Fin n → ℕ))
def columnRaw {n : ℕ} (μ : SparseIntegerLaw ((Fin n → ℕ))) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map ListOperation.setView)
def Input.raw (x : Input) : InputRaw := (List.replicate x.n (),List.ofFn fun i => columnRaw (x.columns i))
abbrev Input.encode (x : Input) := ei x.raw
structure Context where
  input : Input
  t : ℕ
def Context.raw (c : Context) : InputRaw × ℕ := (c.input.raw,c.t)
abbrev Context.encode (c : Context) := encodePair ei Nat.bits c.raw
abbrev T (c : Context) := SparseCounts.Table c.input.n c.input.m
abbrev view (c : Context) (G : T c) := ListOperation.view G
abbrev State := Bundle T
abbrev State.encode := Bundle.encode Context.encode et view

def column (c : Context) : SparseIntegerLaw (Fin c.input.n → ℕ) :=
  if h : c.t<c.input.m then c.input.columns ⟨c.t,h⟩ else .dirac (fun _ => 0)
def update (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) : T c :=
  fun i => if i.val=c.t then S else G i

def rawColumn (x : InputRaw × ℕ) : Data Row :=
  if x.2 < x.1.2.length then x.1.2[x.2]?.getD ((1,[1]),[])
  else ((1,[1]),[x.1.1.map (fun _ => 0)])

theorem rawColumn_eq (c : Context) : rawColumn c.raw=columnRaw (column c) := by
  simp only [rawColumn,Context.raw,Input.raw,List.length_ofFn,List.getElem?_ofFn,column]
  split_ifs with h
  · rfl
  · simp only [columnRaw,SparseIntegerLaw.dirac,Vector.toList_replicate,
      List.map_replicate,List.ofFn_const,ListOperation.setView]
    rfl

theorem update_view (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) :
    ListOperation.nextTable ((c.t,view c G),ListOperation.setView S)=view c (update c G S) := by
  apply List.ext_getElem
  · simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjm : j<c.input.m := by simpa only [view,ListOperation.view,List.length_ofFn] using hj'
    simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,ListOperation.setView,List.getElem_map,
      List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hjm,Option.getD_some,update]
    split_ifs <;> rfl

def State.product (x : State) : State := ⟨x.ctx,x.law.prod (column x.ctx) (update x.ctx)⟩
def rawProduct (x : (InputRaw × ℕ) × Data ListOperation.Table) : (InputRaw × ℕ) × Data ListOperation.Table :=
  let p := prodData (x.2,rawColumn x.1)
  (x.1,(p.1,p.2.map (fun z => ListOperation.nextTable ((x.1.2,z.1),z.2))))

theorem rawProduct_eq (x : State) :
    rawProduct (x.ctx.raw,(x.raw view).2)=((x.product).ctx.raw,((x.product).raw view).2) := by
  unfold rawProduct
  rw [rawColumn_eq]
  simp only [Bundle.raw,columnRaw,State.product,prodData,
    states_list,SparseIntegerLaw.prod,Vector.toList_ofFn,List.map_ofFn,List.flatMap_def,
    Function.comp_def,RoundingList.ofFn_product,Context.raw,update_view]
  rfl

noncomputable def productProgram : PolyProgram State.encode State.encode State.product := by
  have hc : Binary.Automatic.Poly rawColumn := by
    unfold rawColumn
    have hm : Binary.Automatic.Poly (fun x : InputRaw × ℕ => x.1.1.map (fun _ => 0)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  have hp : Binary.Automatic.Poly rawProduct := by
    unfold rawProduct
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.pair
      · fun_prop
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact hp.program.recode (fun x => (x.ctx.raw,(x.raw view).2)) (fun _ => rfl)
    (fun x => congrArg Binary.Automatic.enc (rawProduct_eq x))

noncomputable def dimensionsProgram : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate (c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) ()) :=
  (((fst ei Nat.bits).comp ListOperation.dimensions_poly.program).recode Context.raw (fun _ => rfl)
    (fun c => congrArg _ (ListOperation.dimensions_eq (fun i => columnRaw (c.input.columns i)))))
noncomputable def featuresProgram : PolyProgram (encodePair Context.encode et) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2)) := by
  let p : PolyProgram (encodePair (encodePair ei Nat.bits) et) IntegerLaw.BinaryCompression.eqr
      (fun x : (InputRaw × ℕ) × ListOperation.Table => ListOperation.featureList (x.1.1.1,x.2)) := by
    apply Binary.Automatic.Poly.program
    fun_prop
  exact p.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)

noncomputable def compressProgram : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) (fun _ => features)) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode et view [] _ (fun _ => features)
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2))
    (fun _ G => ListOperation.featureList_view G) dimensionsProgram featuresProgram

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
def State.step (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.m then
    Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m))
      (fun _ => features) x.product else x)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (ed et)
  let inp := old.comp ((fst ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (ed et)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.m)) := by
  let raw : PolyProgram (encodePair ei Nat.bits) encodeBool
      (fun x : InputRaw × ℕ => decide (x.2<x.1.2.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t<c.input.m)) := raw.recode Context.raw (fun _ => rfl)
    (fun c => by simp only [Context.raw,Input.raw,List.length_ofFn])
  exact (contextProgram Context.encode et view).comp ctx
noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  ((PolyProgram.ite activeProgram (identity State.encode) (productProgram.comp compressProgram)).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])
end MetricKMedian.SparseCounts.Program
end

end OAI
