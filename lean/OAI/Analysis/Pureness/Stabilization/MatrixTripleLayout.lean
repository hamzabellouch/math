import OAI.Analysis.Pureness.Stabilization.MatrixSupportedPermutation
import OAI.Analysis.Pureness.Stabilization.MatrixInterleaveSystem

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

private lemma le_double (n : ℕ) : n ≤ n*2 := by omega

def matrixTripleLeftIndex (n : ℕ) (p : Fin 3 × Fin n) : Fin ((n*2)*2) :=
  ![finProdFinEquiv (finProdFinEquiv (p.2,(0 : Fin 2)),(0 : Fin 2)),
    finProdFinEquiv (finProdFinEquiv (p.2,(1 : Fin 2)),(0 : Fin 2)),
    finProdFinEquiv (Fin.castLE (le_double n) p.2,(1 : Fin 2))] p.1

def matrixTripleRightIndex (n : ℕ) (p : Fin 3 × Fin n) : Fin ((n*2)*2) :=
  ![finProdFinEquiv (Fin.castLE (le_double n) p.2,(0 : Fin 2)),
    finProdFinEquiv (finProdFinEquiv (p.2,(0 : Fin 2)),(1 : Fin 2)),
    finProdFinEquiv (finProdFinEquiv (p.2,(1 : Fin 2)),(1 : Fin 2))] p.1

lemma matrixTripleLeftIndex_injective (n : ℕ) : Function.Injective (matrixTripleLeftIndex n) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have he := congrArg Fin.val h
  fin_cases r <;> fin_cases s <;> simp [matrixTripleLeftIndex,finProdFinEquiv] at he <;>
    try omega
  all_goals exact Prod.ext rfl (Fin.ext (by omega))

lemma matrixTripleRightIndex_injective (n : ℕ) : Function.Injective (matrixTripleRightIndex n) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have he := congrArg Fin.val h
  fin_cases r <;> fin_cases s <;> simp [matrixTripleRightIndex,finProdFinEquiv] at he <;>
    try omega
  all_goals exact Prod.ext rfl (Fin.ext (by omega))

def matrixTripleLeft (n : ℕ) (M N P : FinMatrix A n) : FinMatrix A ((n*2)*2) :=
  matrixInterleave (n*2) (matrixInterleave n (M,N),matrixInclusion (le_double n) P)

def matrixTripleRight (n : ℕ) (M N P : FinMatrix A n) : FinMatrix A ((n*2)*2) :=
  matrixInterleave (n*2) (matrixInclusion (le_double n) M,matrixInterleave n (N,P))

lemma matrixTriple_entries (n : ℕ) (M N P : FinMatrix A n) (i j : Fin 3 × Fin n) :
    matrixTripleLeft n M N P (matrixTripleLeftIndex n i) (matrixTripleLeftIndex n j) =
    matrixTripleRight n M N P (matrixTripleRightIndex n i) (matrixTripleRightIndex n j) := by
  obtain ⟨r,i⟩ := i
  obtain ⟨s,j⟩ := j
  fin_cases r <;> fin_cases s <;>
    simp [matrixTripleLeftIndex,matrixTripleRightIndex,matrixTripleLeft,matrixTripleRight,
      matrixInterleave_entry,matrixInclusion_entry_inside]

lemma matrixTripleLeft_outside (n : ℕ) (M N P : FinMatrix A n) (i j : Fin ((n*2)*2))
    (h : i ∉ Set.range (matrixTripleLeftIndex n) ∨ j ∉ Set.range (matrixTripleLeftIndex n)) :
    matrixTripleLeft n M N P i j = 0 := by
  obtain ⟨⟨p,r⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨q,s⟩,rfl⟩ := finProdFinEquiv.surjective j
  have he (p : Fin (n*2)) : finProdFinEquiv (p,(0 : Fin 2)) ∈ Set.range (matrixTripleLeftIndex n) := by
    obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective p
    fin_cases t
    · exact ⟨(0,i),by simp [matrixTripleLeftIndex]⟩
    · exact ⟨(1,i),by simp [matrixTripleLeftIndex]⟩
  have ho (p : Fin (n*2)) (hp : p.val < n) :
      finProdFinEquiv (p,(1 : Fin 2)) ∈ Set.range (matrixTripleLeftIndex n) :=
    ⟨(2,⟨p.val,hp⟩),by simp [matrixTripleLeftIndex]⟩
  change matrixInterleave (n*2) _ _ _ = 0
  rw [matrixInterleave_entry]
  fin_cases r <;> fin_cases s <;> simp
  · exact (h.elim (fun hh => hh (he p)) (fun hh => hh (he q))).elim
  · apply matrixInclusion_entry_outside
    exact h.elim (fun hp => Or.inl (by by_contra hn; exact hp (ho p (by omega))))
      (fun hq => Or.inr (by by_contra hn; exact hq (ho q (by omega))))

lemma matrixTripleRight_outside (n : ℕ) (M N P : FinMatrix A n) (i j : Fin ((n*2)*2))
    (h : i ∉ Set.range (matrixTripleRightIndex n) ∨ j ∉ Set.range (matrixTripleRightIndex n)) :
    matrixTripleRight n M N P i j = 0 := by
  obtain ⟨⟨p,r⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨q,s⟩,rfl⟩ := finProdFinEquiv.surjective j
  have he (p : Fin (n*2)) (hp : p.val < n) :
      finProdFinEquiv (p,(0 : Fin 2)) ∈ Set.range (matrixTripleRightIndex n) :=
    ⟨(0,⟨p.val,hp⟩),by simp [matrixTripleRightIndex]⟩
  have ho (p : Fin (n*2)) : finProdFinEquiv (p,(1 : Fin 2)) ∈ Set.range (matrixTripleRightIndex n) := by
    obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective p
    fin_cases t
    · exact ⟨(1,i),by simp [matrixTripleRightIndex]⟩
    · exact ⟨(2,i),by simp [matrixTripleRightIndex]⟩
  change matrixInterleave (n*2) _ _ _ = 0
  rw [matrixInterleave_entry]
  fin_cases r <;> fin_cases s <;> simp
  · apply matrixInclusion_entry_outside
    exact h.elim (fun hp => Or.inl (by by_contra hn; exact hp (he p (by omega))))
      (fun hq => Or.inr (by by_contra hn; exact hq (he q (by omega))))
  · exact (h.elim (fun hh => hh (ho p)) (fun hh => hh (ho q))).elim

theorem matrixTriple_permutation (n : ℕ) (M N P : FinMatrix A n) :
    ∃ e : Equiv.Perm (Fin ((n*2)*2)), matrixPermute e (matrixTripleLeft n M N P) = matrixTripleRight n M N P :=
  matrix_supported_permutation
    ⟨matrixTripleLeftIndex n,matrixTripleLeftIndex_injective n⟩
    ⟨matrixTripleRightIndex n,matrixTripleRightIndex_injective n⟩ _ _
    (matrixTriple_entries n M N P) (matrixTripleLeft_outside n M N P) (matrixTripleRight_outside n M N P)
end CuntzTrace

end

end OAI
