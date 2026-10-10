import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptionsFinite

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
variable {A Ω : Type} [LinearOrder A] [LinearOrder Ω]
omit [LinearOrder A] [LinearOrder Ω] in
lemma repr_map (e : Ω→A) (c : WeightedOptions Ω) :
    repr e c=(repr id c).map (fun a=>(e a.1,a.2)) := by
  simp only [repr,List.map_ofFn,Function.comp_def,id_eq]

lemma uniform_map (e : Ω↪oA) (s : Finset Ω) :
    uniform (s.map e.toEmbedding)=(uniform s).map (fun a=>(e a.1,a.2)) := by
  unfold uniform
  rw [Finset.card_map,←Finset.map_sort (r:=fun x y : Ω=>x≤y) (r':=fun x y : A=>x≤y)
    (f:=e.toEmbedding) (s:=s) (fun a _ b _=>(e.le_iff_le).symm)]
  simp only [List.map_map,Function.comp_def]
  rfl
lemma uniform_repr_map (e : Ω↪oA) (s : Finset Ω) (hs : s.Nonempty) :
    uniform (s.map e.toEmbedding)=repr e (WeightedOptions.uniform s hs) := by
  rw [uniform_map,uniform_repr s hs,repr_map e]

lemma neighbors_map (e : Ω↪oA) (a : Ω) (s : Finset Ω) (d : ℕ) :
    neighbors ((e a,s.map e.toEmbedding),d)=
      (neighbors ((a,s),d)).map (fun a=>(e a.1,a.2)) := by
  unfold neighbors
  rw [Finset.card_map,←Finset.map_sort (r:=fun x y : Ω=>x≤y) (r':=fun x y : A=>x≤y)
    (f:=e.toEmbedding) (s:=s) (fun a _ b _=>(e.le_iff_le).symm)]
  simp only [List.map_map,List.map_append,List.map_cons,List.map_nil,Function.comp_def]
  rfl
lemma neighbors_repr_map (e : Ω↪oA) (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card≤d) :
    neighbors ((e a,s.map e.toEmbedding),d)=repr e (WeightedOptions.neighbors a s d hd) := by
  rw [neighbors_map,neighbors_repr a s d hd,repr_map e]
end MatchingFPRAS.ExecutableOptions

end OAI
