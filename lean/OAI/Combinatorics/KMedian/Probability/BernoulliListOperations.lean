import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliFeatures
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev Row := List Bool
abbrev er := encodeList encodeBool

def units : ℕ → Row → List Unit
  | 0,_ => [()]
  | d+1,q => (false::q).flatMap (fun _ => units d q)

@[fun_prop] theorem units_poly (d : ℕ) : Poly (units d) := by
  induction d with
  | zero => exact const [()]
  | succ d ih =>
    change Poly (fun q => (false::q).flatMap (fun _ => units d q))
    apply list_flatMap
    · exact comp ih fst
    · fun_prop

@[simp] theorem units_length (d : ℕ) (q : Row) : (units d q).length=(q.length+1)^d := by
  induction d with
  | zero => simp [units]
  | succ d ih => simp [units,List.length_flatMap,ih,pow_succ,Nat.mul_comm]; ring

theorem units_eq (d : ℕ) (q : Row) : units d q=List.replicate ((q.length+1)^d) () := by
  rw [← units_length d q]
  exact List.eq_replicate_length.mpr (fun b hb => Subsingleton.elim _ _)

def tests (d : ℕ) (q : Row) (j : ℕ) : List Bool :=
  (List.range d).map (fun a => q[j/(q.length+1)^a%(q.length+1)]?.getD true)
def value (d : ℕ) (q : Row) (j : ℕ) : ℚ := if (tests d q j).all id then 1 else 0
def featureList (d : ℕ) (q : Row) : List ℚ :=
  (List.range (units d q).length).map (value d q)

@[fun_prop] theorem tests_poly (d : ℕ) : Poly (fun x : Row × ℕ => tests d x.1 x.2) := by
  apply fixed_map
  intro a ha
  have hp : Poly (fun q : Row => (q.length+1)^a) := comp (nat_pow a) (by fun_prop)
  fun_prop
@[fun_prop] theorem value_poly (d : ℕ) : Poly (fun x : Row × ℕ => value d x.1 x.2) := by
  unfold value
  fun_prop
@[fun_prop] theorem featureList_poly (d : ℕ) : Poly (featureList d) := by
  apply list_map
  · exact comp (value_poly d) (by fun_prop)
  · exact comp (f:=fun xs : List Unit => List.range xs.length) (g:=units d) list_indices (units_poly d)

 theorem flag_product {n : ℕ} (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i) = if ∀ i∈S, q i=true then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,ih]
    by_cases hq : q i=true <;> by_cases hs : ∀j∈S,q j=true <;> simp [flag,hq,hs]

 theorem get_true_iff {n : ℕ} (q : Fin n → Bool) (k : ℕ) :
    ((List.ofFn q)[k]?.getD true)=true ↔ ∀ i : Fin n, k=i.val → q i=true := by
  by_cases hk : k<n
  · simp only [List.getElem?_ofFn, dite_eq_left hk]
    simp only [Option.getD_some]
    constructor
    · intro h i hi
      have he : i=(⟨k,hk⟩ : Fin n) := Fin.ext hi.symm
      simpa only [he] using h
    · intro h; exact h ⟨k,hk⟩ rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    simp only [Option.getD_none,true_iff]
    intro i hi
    exact (hk (hi ▸ i.isLt)).elim

 theorem tests_true_iff {n degree : ℕ} (q : Fin n → Bool) (j : Fin ((n+1)^degree)) :
    (tests degree (List.ofFn q) j.val).all id=true ↔ ∀ i∈used (finFunctionFinEquiv.symm j), q i=true := by
  simp only [tests,List.all_map,List.all_eq_true,Function.comp_def,id_eq,List.mem_range,List.length_ofFn]
  constructor
  · intro h i hi
    obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hi).2
    apply (get_true_iff q _).mp (h a.val a.isLt) i
    exact ha
  · intro h a ha
    apply (get_true_iff q _).mpr
    intro i hi
    apply h i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨a,ha⟩,hi⟩⟩

 theorem featureList_ofFn {n degree : ℕ} (q : Fin n → Bool) :
    featureList degree (List.ofFn q)=List.ofFn (features (d:=degree) q) := by
  apply List.ext_getElem
  · simp [featureList]
  · intro i hi hi'
    have hi'' : i<(n+1)^degree := by simpa [featureList] using hi
    simp only [featureList,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold value features monomial
    rw [flag_product]
    congr 1
    exact propext (tests_true_iff q ⟨i,hi''⟩)

 def endpoint (t : ℕ) (b : Bool) (q : Row) : Row :=
   (List.range q.length).map (fun i => if i=t then b else q[i]?.getD false)
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : ℕ × Row => endpoint x.1 b x.2) := by
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=Prod.snd) list_indices snd
 theorem endpoint_ofFn {n : ℕ} (q : Fin n → Bool) (i : Fin n) (b : Fin 2) :
    endpoint i.val (decide (b=0)) (List.ofFn q)=List.ofFn (SparseBernoulli.endpoint q i b) := by
  apply List.ext_getElem
  · simp only [endpoint,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjn : j<n := by simpa only [List.length_ofFn] using hj'
    simp only [endpoint,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      List.getElem?_ofFn,dite_eq_left hjn,Option.getD_some]
    change (if j=i.val then _ else q ⟨j,hjn⟩)=(if (⟨j,hjn⟩ : Fin n)=i then _ else q ⟨j,hjn⟩)
    simp only [Fin.ext_iff]

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
