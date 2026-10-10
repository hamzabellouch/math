import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalKernel
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {f Δ : ℕ}
local instance : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

abbrev rank (a : CopyState.Copy (F:=Fin f) Δ) : Fin (f*Δ) := finProdFinEquiv a

def view (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : Row := setView (A.map finProdFinEquiv.toEmbedding)
def active (A : Row) : List ℕ := (indices A).filter (fun i => A[i]?.getD false)
@[fun_prop] theorem active_poly : Poly active := by unfold active; apply list_filter <;> fun_prop

 theorem rank_strictMono : @StrictMono _ _ (copyOrder (F:=Fin f) (Δ:=Δ)).toPreorder _ (rank (f:=f) (Δ:=Δ)) := by
  intro a b hab
  change Prod.Lex (fun a b : Fin f => a<b) (fun a b : Fin Δ => a<b) a b at hab
  change a.2.val+Δ*a.1.val<b.2.val+Δ*b.1.val
  rcases Prod.lex_def.mp hab with h | ⟨h,h'⟩
  · have h1 : a.1.val+1≤b.1.val := h
    have h2 := a.2.isLt
    nlinarith
  · rw [h]
    have h2 : a.2.val<b.2.val := h'
    omega
abbrev activeOrder (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A :=
  @Subtype.instLinearOrder _ (copyOrder (F:=Fin f) (Δ:=Δ)) (·∈A)
 theorem enum_rank_strictMono (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    StrictMono (fun i => (rank (enumeration A i).val).val) := by
  intro i j hij
  apply rank_strictMono
  exact @OrderIso.strictMono _ _ _ (activeOrder A).toPreorder
    (@Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)) i j hij
 theorem active_view (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    active (view A)=List.ofFn (fun i => (rank (enumeration A i).val).val) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (enum_rank_strictMono A).sortedLT_ofFn
  · intro k
    simp only [active,indices,view,setView,List.length_ofFn,List.mem_filter,List.mem_range,List.mem_ofFn]
    constructor
    · rintro ⟨hk,ha⟩
      simp only [List.getElem?_ofFn,dite_eq_left hk,Option.getD_some,decide_eq_true_eq,mem_map_equiv] at ha
      let a : A := ⟨finProdFinEquiv.symm ⟨k,hk⟩,ha⟩
      refine ⟨(enumeration A).symm a,?_⟩
      rw [Equiv.apply_symm_apply]
      change ((finProdFinEquiv (finProdFinEquiv.symm ⟨k,hk⟩)).val)=k
      rw [Equiv.apply_symm_apply]
    · rintro ⟨i,rfl⟩
      refine ⟨(rank (enumeration A i).val).isLt,?_⟩
      simp only [List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,
        mem_map_equiv,Equiv.symm_apply_apply]
      exact (enumeration A i).property

 def ordinal (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :=
  @Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)
 theorem ordinal_enum (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : (ordinal A).toEquiv=enumeration A := rfl

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
