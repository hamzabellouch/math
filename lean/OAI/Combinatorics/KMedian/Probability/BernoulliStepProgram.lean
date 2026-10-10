import Mathlib
import OAI.Combinatorics.KMedian.Programs.DependentSparseProgram
import OAI.Combinatorics.KMedian.Probability.BernoulliListOperations

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev Row := ListOperation.Row
abbrev er := ListOperation.er
abbrev qr := encodeList Ratio.encode

structure Input where
  n : ℕ
  p : Fin n → ℚ
  feasible : ∀ i, 0 ≤ p i ∧ p i ≤ 1
abbrev Input.encode (x : Input) := qr (List.ofFn x.p)
structure Context where
  input : Input
  t : ℕ
abbrev Context.raw (c : Context) := (List.ofFn c.input.p,c.t)
abbrev Context.encode (c : Context) := encodePair qr Nat.bits c.raw
abbrev T (c : Context) := Fin c.input.n → Bool
abbrev view (c : Context) (q : T c) := List.ofFn q
abbrev State := Bundle T
abbrev State.encode := Bundle.encode Context.encode er view

def probability (c : Context) (_ : T c) : ℚ := if h : c.t<c.input.n then c.input.p ⟨c.t,h⟩ else 0
def endpoint (c : Context) (q : T c) (b : Fin 2) : T c :=
  fun i => if i.val=c.t then decide (b=0) else q i
 theorem probability_unit (c : Context) (q : T c) : 0 ≤ probability c q ∧ probability c q ≤ 1 := by
  unfold probability
  split_ifs with h
  · exact c.input.feasible _
  · norm_num

def rowProbability (x : Context × Row) : ℚ := x.1.raw.1[x.1.t]?.getD 0
def rowEndpoint (b : Bool) (x : Context × Row) : Row := ListOperation.endpoint x.1.t b x.2
 theorem probability_view (c : Context) (q : T c) : rowProbability (c,view c q)=probability c q := by
  simp only [rowProbability,probability,view,List.getElem?_ofFn]
  split_ifs <;> rfl
 theorem endpoint_view (c : Context) (q : T c) (b : Fin 2) :
    rowEndpoint (decide (b=0)) (c,view c q)=view c (endpoint c q b) := by
  apply List.ext_getElem
  · simp only [rowEndpoint,ListOperation.endpoint,List.length_map,List.length_range,view,List.length_ofFn]
  · intro i hi hi'
    have hin : i<c.input.n := by simpa only [view,List.length_ofFn] using hi'
    simp only [rowEndpoint,ListOperation.endpoint,view,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some,endpoint]

noncomputable def probabilityProgram : PolyProgram (encodePair Context.encode er) Ratio.encode rowProbability := by
  let raw : PolyProgram (encodePair (encodePair qr Nat.bits) er) Ratio.encode
      (fun x : (List ℚ × ℕ) × Row => x.1.1[x.1.2]?.getD 0) := by
    exact Binary.Automatic.Poly.program (by fun_prop)
  exact raw.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)
noncomputable def endpointProgram (b : Bool) : PolyProgram (encodePair Context.encode er) er (rowEndpoint b) :=
  (((fst Context.encode er).comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))).fanout
     (snd Context.encode er)).comp (ListOperation.endpoint_poly b).program

noncomputable def branchProgram : PolyProgram State.encode State.encode (Bundle.branch probability probability_unit endpoint) :=
  SparseIntegerLaw.DependentProgram.branchProgram Context.encode er view [] probability probability_unit endpoint
    rowProbability (rowEndpoint true) (rowEndpoint false) probability_view
    (fun c q => endpoint_view c q 0) (fun c q => endpoint_view c q 1)
    probabilityProgram (endpointProgram true) (endpointProgram false)

noncomputable def dimensionsProgram (d : ℕ) : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate ((c.input.n+1)^d) ()) := by
  let raw : PolyProgram (encodePair qr Nat.bits) IntegerLaw.BinaryCompression.es
      (fun x : List ℚ × ℕ => ListOperation.units d (x.1.map (fun _ => false))) := by
    apply Binary.Automatic.Poly.program
    exact Binary.Automatic.Poly.comp (ListOperation.units_poly d) (by
      apply Binary.Automatic.Poly.list_map <;> fun_prop)
  exact raw.recode Context.raw (fun _ => rfl) (fun c => by
    simp only [ListOperation.units_eq,List.length_map,List.length_ofFn])
noncomputable def featuresProgram (d : ℕ) : PolyProgram (encodePair Context.encode er) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList d x.2) :=
  (snd Context.encode er).comp (ListOperation.featureList_poly d).program

noncomputable def compressProgram (d : ℕ) : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode er view [] (fun c => (c.input.n+1)^d) (fun _ => features (d:=d))
    (fun x => ListOperation.featureList d x.2) (fun _ q => ListOperation.featureList_ofFn q)
    (dimensionsProgram d) (featuresProgram d)

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
def State.step (d : ℕ) (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.n then
    Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))
      (Bundle.branch probability probability_unit endpoint x)
    else x)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  let inp := old.comp ((fst qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.n)) := by
  let raw : PolyProgram (encodePair qr Nat.bits) encodeBool
      (fun x : List ℚ × ℕ => decide (x.2<x.1.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t<c.input.n)) := raw.recode Context.raw (fun _ => rfl) (fun c => by simp only [List.length_ofFn])
  exact (contextProgram Context.encode er view).comp ctx
noncomputable def stepProgram (d : ℕ) : PolyProgram State.encode State.encode (State.step d) :=
  ((PolyProgram.ite activeProgram (identity State.encode) (branchProgram.comp (compressProgram d))).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])

end MetricKMedian.SparseBernoulli.Program
end

end OAI
