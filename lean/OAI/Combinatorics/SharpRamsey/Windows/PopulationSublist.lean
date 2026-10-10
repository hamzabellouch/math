import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.GoodPopulation

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section

lemma finProd_position {w n : ℕ} (i : Slot w n) :
    (finProdFinEquiv i).val=position i := by
  simp [finProdFinEquiv,position,Nat.mul_comm,Nat.add_comm]

def flattenTuple {β : Type*} {w n : ℕ} (F : Slot w n→β) : Fin (w*(4*n))→β :=
  fun i=>F (finProdFinEquiv.symm i)

variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)
local instance sublistFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance sublistIndexDec (z : (model w n k p θ G t).FreshHistory) :
    DecidableEq ((model w n k p θ G t).Index z.1) := Classical.decEq _

theorem goodPopulation_sublist {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1))
    (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) (F0 : Slot w (n+k)→A×B)
    (hF : ∀ i,F i=F0 ((model w n k p θ G t).origin z.1 i)) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).Sublist (List.ofFn (flattenTuple F0)) := by
  let l:=population (fun i=>List.ofFn (fun j=>(model w n k p θ G t).origin z.1
    (goodTarget w n k p θ G t z bad i j))) (liveTree live fallback)
  have hl : l.Pairwise (fun i j=>position i<position j) :=
    goodPopulation_pairwise w n k p θ G t z bad live fallback
      ((model w n k p θ G t).origin z.1) (fun i j=>position i<position j) (fun _ _ h=>h)
  have hl' : (l.map finProdFinEquiv).Pairwise (·<·) := by
    rw [List.pairwise_map]
    apply hl.imp
    intro i j hij
    change (finProdFinEquiv i).val<(finProdFinEquiv j).val
    simpa only [finProd_position] using hij
  have hs : (l.map finProdFinEquiv).Sublist (List.finRange (w*(4*(n+k)))) :=
    List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset hl'.nodup (by intro i hi;exact List.mem_finRange i))
      hl' (List.sortedLT_finRange _).pairwise
  have hm:=hs.map (flattenTuple F0)
  rw [←List.ofFn_eq_map] at hm
  simpa [l,population_flatMap,List.map_flatMap,List.map_ofFn,Function.comp_def,
    flattenTuple,←hF] using hm
end
end SharpLogRamsey.Selection.Windows

end

end OAI
