import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

variable (I : Type*) [Fintype I]

def listPool (N : ℕ) : Finset (List I) := by
  classical
  exact Finset.univ.biUnion (fun n : Fin (N+1) =>
    Finset.univ.image (fun f : Fin n → I => List.ofFn f))

lemma mem_listPool (N : ℕ) (l : List I) : l∈listPool I N ↔ l.length ≤ N := by
  classical
  constructor
  · intro h
    simp only [listPool,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and] at h
    obtain ⟨n,f,rfl⟩ := h
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ n.isLt
  · intro h
    simp only [listPool,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and]
    exact ⟨⟨l.length,Nat.lt_succ_of_le h⟩,l.get,List.ofFn_get l⟩

abbrev SmallList (N : ℕ) := ↥(listPool I N)

def smallList {N : ℕ} (l : List I) (h : l.length ≤ N) : SmallList I N :=
  ⟨l,(mem_listPool I N l).mpr h⟩

lemma SmallList.length_le {N : ℕ} (l : SmallList I N) : l.val.length ≤ N :=
  (mem_listPool I N l.val).mp l.property

end Kadison.FinitePatching

end

end
end

end OAI
