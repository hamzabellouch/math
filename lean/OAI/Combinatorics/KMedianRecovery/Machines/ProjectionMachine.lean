import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets
import OAI.Combinatorics.KMedianRecovery.Recovery.CanonicalParents

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryProjection
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
noncomputable def run (x : List Bool) : List Bool :=
  BinaryNatSet.sort (WordList.map BinaryLabel.parentWords x)
noncomputable def run_computes : PolyComputes run :=
  (map_computes BinaryLabel.parentWords_computes).comp BinaryNatSet.sort_computes
lemma run_labels {m : ℕ} (xs : List (Label (Fin m))) :
    run (labels xs)=BinaryFinSet.encode (xs.toFinset.image parent) := by
  simp only [run,labels,map_encode,List.map_map,Function.comp_def,BinaryLabel.parentWords_encode]
  have hh:=BinaryNatSet.sort_pack (xs.map (fun x=>(parent x).val))
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_map,BinaryFinSet.values,Finset.mem_image]
  exact ⟨fun ⟨x,hx,he⟩=>⟨parent x,⟨x,hx,rfl⟩,he⟩,fun ⟨j,⟨x,hx,he⟩,hj⟩=>⟨x,hx,by simpa only [he] using hj⟩⟩
lemma run_setBits {m : ℕ} (Q : Finset (Label (Fin m))) :
    run (setBits Q)=BinaryFinSet.encode (RationalLeaves.project Q) := by
  rw [setBits,run_labels]
  simp only [BinaryLabel.orderedSort,Finset.sort_toFinset,project]
noncomputable def originalWord (x : List Bool) : List Bool :=
  pairBits ((0:ℕ).bits,pairBits (x,BinaryRational.encode 0))
noncomputable def originalWord_computes : PolyComputes originalWord :=
  (const_computes _).pair (id_computes.pair (const_computes _))
noncomputable def lift (x : List Bool) : List Bool :=
  BinaryLabel.sort (WordList.map originalWord x)
noncomputable def lift_computes : PolyComputes lift :=
  (map_computes originalWord_computes).comp BinaryLabel.sort_computes
lemma lift_encode {m : ℕ} (S : Finset (Fin m)) :
    lift (BinaryFinSet.encode S)=setBits (S.image original) := by
  rw [lift,BinaryFinSet.encode_eq,map_encode,List.map_map]
  simp only [Function.comp_def]
  have hf : (fun i : Fin m=>originalWord i.val.bits)=(fun i=>BinaryLabel.encode (original i)) := by
    funext i
    rfl
  rw [hf]
  change BinaryLabel.sort (WordList.encode ((S.sort (·≤·)).map (BinaryLabel.encode ∘ original)))=_
  rw [←List.map_map,BinaryLabel.sort_encode]
  have hs : ((S.sort (·≤·)).map original).toFinset=S.image original := by
    ext x
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image]
  change setBits (((S.sort (·≤·)).map original).toFinset)=setBits (S.image original)
  rw [hs]
end MetricKMedianRecovery.BitMachine.BinaryProjection

end OAI
