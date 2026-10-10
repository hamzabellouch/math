import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeNumberedCodec

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
def embedding : A ↪ ℕ := ⟨index,index_injective⟩
def set (s : Finset A) : Finset ℕ := s.map embedding
lemma sort_set (s : Finset A) : (set s).sort (·≤·)=(s.sort (·≤·)).map index := by
  symm
  exact Finset.map_sort embedding s (·≤·) (·≤·) (fun a _ b _=>(index_le a b).symm)
lemma encode_set (s : Finset A) : encode (set s)=encode s := by
  rw [encode_finset,sort_set,encode_finset]
  change TreeData.ofList (((s.sort (·≤·)).map index).map encode)=
    TreeData.ofList ((s.sort (·≤·)).map (fun a=>encode (index a)))
  simp only [List.map_map, Function.comp_def]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
