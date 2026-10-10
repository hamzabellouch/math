import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedPartial
import OAI.Combinatorics.KMedian.Rounding.SignedListOperations
import OAI.Combinatorics.KMedian.Sparse.SparseBranchProgram

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly

def features (p : Row) : Row := p ++ p.flatMap (fun x => p.map (fun y => x*y))
def dimensions (p : Row) : List Unit := (indices p).map (fun _ => ()) ++ (square p).map (fun _ => ())

@[fun_prop] theorem features_poly : Poly features := by
  have h : Poly (fun p : Row => p.flatMap (fun x => p.map (fun y => x*y))) := by
    apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
  exact comp (f:=fun x : Row × Row => x.1++x.2)
    (g:=fun p : Row => (p,p.flatMap (fun x => p.map (fun y => x*y)))) list_append (pair identity h)
@[fun_prop] theorem dimensions_poly : Poly dimensions := by
  have h1 : Poly (fun p : Row => (indices p).map (fun _ => ())) := by
    apply list_map <;> fun_prop
  have h2 : Poly (fun p : Row => (square p).map (fun _ => ())) := by
    apply list_map <;> fun_prop
  exact comp (f:=fun x : List Unit × List Unit => x.1++x.2)
    (g:=fun p : Row => ((indices p).map (fun _ => ()),(square p).map (fun _ => ()))) list_append (pair h1 h2)

theorem dimensions_list {n : ℕ} (β : Fin n → ℚ) :
    dimensions (List.ofFn β)=List.replicate (n+n*n) () := by
  simp only [dimensions,indices,square,List.length_ofFn]
  simp

theorem features_list {n : ℕ} (p : Vector ℚ n) :
    features p.toList=List.ofFn (SparseWeightedPartial.features p) := by
  have hp : p.toList=List.ofFn (RationalWeightedStep.point p) := by
    apply List.ext_getElem <;> intros <;> simp [RationalWeightedStep.point]
  simp only [features,hp,List.flatMap_def,List.map_ofFn,Function.comp_def,ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd (n*n) i : Fin (n+n*n))=finSumFinEquiv (Sum.inl i) := by rfl
    change _=SparseWeightedPartial.features p (Fin.castAdd (n*n) i)
    rw [hi,SparseWeightedPartial.features_single]
  · congr 1; funext i
    have hi : (Fin.natAdd n i : Fin (n+n*n))=finSumFinEquiv (Sum.inr i) := by
      apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [SparseWeightedPartial.features,Equiv.symm_apply_apply,Sum.elim_inr]

end MetricKMedian.RoundingList

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
abbrev Row := RoundingList.Row
abbrev erow := RoundingList.er

structure State (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  positive : signed=false → ∀ i, 0<β i
  μ : SparseIntegerLaw (Vector ℚ n)

def State.encode {s : Bool} (x : State s) : List Bool :=
  encodePair erow (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList)) (List.ofFn x.β,x.μ)
def State.raw {s : Bool} (x : State s) : Row × Data Row :=
  (List.ofFn x.β,((x.μ.law.denominator,List.ofFn x.μ.law.numerator),x.μ.states.toList.map Vector.toList))

theorem encodeList_map {α β : Type} (eb : β → List Bool) (f : α → β) (xs : List α) :
    encodeList eb (xs.map f)=encodeList (fun x => eb (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, encodeList,ih]

theorem State.encode_raw {s : Bool} (x : State s) :
    encodePair erow (ed erow) x.raw=x.encode := by
  simp only [State.raw,State.encode,SparseIntegerLaw.BinarySparse.encode,
    SparseIntegerLaw.BinarySparse.raw,ed,encodePair,encodeList_map]

def State.branch {s : Bool} (x : State s) : State s :=
  { x with μ := (if hs : s=true then
      x.μ.branch (RationalSignedStep.probability x.β) (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)
      else x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive (by simpa using hs))) (RationalWeightedStep.endpoint x.β)) }

def State.compressionInput {s : Bool} (x : State s) : IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.μ.length,x.n+x.n*x.n,x.μ.law,fun i => SparseWeightedPartial.features x.μ.states[i.val]⟩
def State.compress {s : Bool} (x : State s) : State s :=
  { x with μ := x.μ.compressAuto SparseWeightedPartial.features }
def State.step {s : Bool} (x : State s) : State s := x.branch.compress

def probability (s : Bool) : Row × Row → ℚ :=
  if s then fun x => RoundingList.Signed.probability x.1 x.2 else fun x => RoundingList.probability x.1 x.2
def endpoint (s b : Bool) : Row × Row → Row :=
  if s then fun x => RoundingList.Signed.endpoint x.1 x.2 b else fun x => RoundingList.endpoint x.1 x.2 b

noncomputable def probabilityProgram (s : Bool) : PolyProgram (encodePair erow erow) Ratio.encode (probability s) := by
  cases s
  · exact RoundingList.probability_poly.program
  · exact RoundingList.Signed.probability_poly.program
noncomputable def endpointProgram (s b : Bool) : PolyProgram (encodePair erow erow) erow (endpoint s b) := by
  cases s
  · exact (RoundingList.endpoint_poly b).program
  · exact (RoundingList.Signed.endpoint_poly b).program

noncomputable def branchRawProgram (s : Bool) :
    PolyProgram (encodePair erow (ed erow)) (encodePair erow (ed erow)) (fun x =>
      (x.1,(branchLawData (x.2.1,x.2.2.map (fun p => probability s (x.1,p))),
        x.2.2.flatMap (fun p => [endpoint s false (x.1,p),endpoint s true (x.1,p)])))) := by
  let β := fst erow (ed erow)
  let law := (snd erow (ed erow)).comp (fst el (encodeList erow))
  let states := (snd erow (ed erow)).comp (snd el (encodeList erow))
  let probs := (β.fanout states).comp ((probabilityProgram s).listMapWith [] 0)
  let laws := (law.fanout probs).comp branchLawProgram
  let endpoints := ((endpointProgram s false).fanout (endpointProgram s true)).comp pairList
  let ps := (β.fanout states).comp (endpoints.listFlatMapWith [] [])
  exact (β.fanout (laws.fanout ps)).congr _ (fun _ => rfl)

end MetricKMedian.RoundingProgram
end

end OAI
