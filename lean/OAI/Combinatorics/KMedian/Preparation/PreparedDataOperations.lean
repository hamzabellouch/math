import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedLaw
import OAI.Combinatorics.KMedian.Binary.BinaryNatSum
import OAI.Combinatorics.KMedian.Rounding.SignedPreparationProgram

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)
abbrev QRow := List ℚ
abbrev NRow := List ℕ
abbrev BTable := List (List Bool)
abbrev StateRaw := SparseSignedPreparation.Program.StateRaw

abbrev BaseRaw := BTable × (QRow × (BTable × (QRow × (QRow × ℕ))))
abbrev KernelRaw := BaseRaw × StateRaw
structure KernelInput where
  n : ℕ
  m : ℕ
  f : ℕ
  D : Fin m → Finset (Fin n)
  q : Fin m → ℚ
  P : Fin n → Finset (Fin f)
  y : Fin f → ℚ
  p : Fin n → ℚ
  Δ : ℕ
  z : SparseSignedPreparation.State n m
  hy : ∀ i,0≤y i
  hp : ∀ j,0<p j

def KernelInput.base (x : KernelInput) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
def KernelInput.raw (x : KernelInput) : KernelRaw := (x.base,SparseSignedPreparation.Program.view x.z)
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

def activationData (x : KernelRaw) (e j : ℕ) : ℕ :=
  (if (x.1.1[e]?.getD [])[j]?.getD false then ⌊x.1.2.1[e]?.getD 0⌋₊ else 0)+
    if (x.2.2.1[e]?.getD [])[j]?.getD false then 1 else 0
def totalData (x : KernelRaw) (j : ℕ) : ℕ :=
  x.1.2.2.2.2.2-min ((indices x.1.2.1).map (fun e => activationData x e j)).sum (x.1.2.2.2.2.2/2)
def pieces (x : KernelRaw) : List (List ℚ) :=
  (indices x.1.2.2.2.2.1).map (fun j => (indices x.1.2.2.2.1).map (fun i =>
    if (x.1.2.2.1[j]?.getD [])[i]?.getD false then
      (totalData x j:ℚ)*x.1.2.2.2.1[i]?.getD 0/x.1.2.2.2.2.1[j]?.getD 0 else 0))
@[fun_prop] theorem activationData_poly : Poly (fun x : KernelRaw × (ℕ × ℕ) => activationData x.1 x.2.1 x.2.2) := by
  unfold activationData; fun_prop
@[fun_prop] theorem totalData_poly : Poly (fun x : KernelRaw × ℕ => totalData x.1 x.2) := by
  unfold totalData
  have h : Poly (fun x : KernelRaw × ℕ => ((indices x.1.1.2.1).map (fun e => activationData x.1 e x.2)).sum) := by
    apply comp nat_list_sum
    apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem pieces_poly : Poly pieces := by
  unfold pieces
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop

theorem activationData_view (x : KernelInput) (e : Fin x.m) (j : Fin x.n) :
    activationData x.raw e.val j.val=SparseOuterLaw.activationCount x.D x.q x.z e j := by
  simp only [activationData,KernelInput.raw,KernelInput.base,SparseSignedPreparation.Program.view,
    SparseGraph.ListOperation.view,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    decide_eq_true_eq,Fin.eta,SparseOuterLaw.activationCount,SparseGridRounding.base]

theorem totalData_view (x : KernelInput) (j : Fin x.n) :
    totalData x.raw j.val=total x.D x.q x.Δ x.z j := by
  unfold totalData
  simp only [KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change x.Δ-min ((List.ofFn (fun e => activationData x.raw e.val j.val)).sum) (x.Δ/2)=_
  simp only [activationData_view,List.sum_ofFn,total]

theorem pieces_view (x : KernelInput) : pieces x.raw=
    List.ofFn (fun j => List.ofFn (fun i => SparseRescaledInner.piece x.P x.y x.p (total x.D x.q x.Δ x.z) i j)) := by
  simp only [pieces,KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,decide_eq_true_eq,Fin.eta]
  change (List.ofFn (fun j : Fin x.n => List.ofFn (fun i : Fin x.f => if i∈x.P j then
    (totalData x.raw j.val:ℚ)*x.y i/x.p j else 0)))=_
  simp only [totalData_view,SparseRescaledInner.piece]
end MetricKMedian.SparsePrepared.Program
end

end OAI
