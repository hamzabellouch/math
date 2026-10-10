import Mathlib
import OAI.Combinatorics.KMedian.Preparation.AssignmentCopies
import OAI.Combinatorics.KMedian.Process.CopyListEncoding

namespace OAI


                                         
section
namespace MetricKMedian.CopyState.CountsProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open RationalPhysicalKernel.CopyList

def mask (Δ : ℕ) (ns : List ℕ) : Row :=
  (indices ns).flatMap (fun i => (List.range Δ).map (fun s => decide (s<ns[i]?.getD 0)))
@[fun_prop] theorem mask_poly (Δ : ℕ) : Poly (mask Δ) := by
  unfold mask
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
 theorem mask_view {f Δ : ℕ} (n : Fin f → ℕ) (hn : ∀ i, n i≤Δ) :
    mask Δ (List.ofFn n)=view (activeSlots n hn) := by
  simp only [mask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,
    Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    List.flatMap_def]
  unfold view setView
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext s
  have he : (⟨i.val*Δ+s.val,by have hi := Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt i.isLt); have hs := s.isLt; nlinarith⟩ : Fin (f*Δ))=rank (i,s) := by
    apply Fin.ext
    change i.val*Δ+s.val=s.val+Δ*i.val
    ac_rfl
  simp only [he,rank,mem_map_equiv,Equiv.symm_apply_apply]
  congr 1
  apply propext
  constructor
  · intro hs
    exact mem_image.mpr ⟨⟨i,⟨s.val,hs⟩⟩,mem_univ _,by rfl⟩
  · intro hs
    obtain ⟨⟨a,t⟩,_,ht⟩ := mem_image.mp hs
    have hi : a=i := congrArg Prod.fst ht
    subst a
    have ht' : t.val=s.val := congrArg (fun x : Copy (F:=Fin f) Δ => x.2.val) ht
    exact ht' ▸ t.isLt
end MetricKMedian.CopyState.CountsProgram
end

end OAI
