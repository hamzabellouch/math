import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixCorners
import OAI.Analysis.JiangSu.TraceCone.MatrixPositive

namespace OAI

noncomputable section
open scoped CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem matrixInclusion_entry_inside {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) (i j : Fin n) :
    matrixInclusion h M (Fin.castLE h i) (Fin.castLE h j) = M i j := by
  change matrixPad h M (Fin.castLE h i) (Fin.castLE h j) = M i j
  induction m, h using Nat.le_induction with
  | base => rw [matrixPad_self]; rfl
  | succ m h ih =>
    rw [matrixPad_succ h]
    change matrixSuccessor m (matrixPad h M) (Fin.castLE h i).castSucc (Fin.castLE h j).castSucc = M i j
    rw [matrixSuccessor_apply_castSucc,ih]

theorem matrixInclusion_entry_outside {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n)
    (i j : Fin m) (hij : n ≤ i.val ∨ n ≤ j.val) : matrixInclusion h M i j = 0 := by
  change matrixPad h M i j = 0
  induction m, h using Nat.le_induction with
  | base => rcases hij with hi | hj <;> omega
  | succ m h ih =>
    rw [matrixPad_succ h]
    revert hij
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro _
      change Fin.lastCases (0 : A)
        (fun i => Fin.lastCases (0 : A) (matrixPad h M i) j) (Fin.last m) = (0 : A)
      simp
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        change Fin.lastCases (0 : A)
          (fun i => Fin.lastCases (0 : A) (matrixPad h M i) (Fin.last m)) i.castSucc = (0 : A)
        simp
      · intro hij
        rw [matrixSuccessor_apply_castSucc]
        exact ih i j hij

theorem matrixInclusion_entry {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) (i j : Fin m) :
    matrixInclusion h M i j =
      if hi : i.val < n then if hj : j.val < n then M ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0 else 0 := by
  split_ifs with hi hj
  · exact matrixInclusion_entry_inside h M ⟨i.val,hi⟩ ⟨j.val,hj⟩
  · exact matrixInclusion_entry_outside h M i j (Or.inr (Nat.le_of_not_gt hj))
  · exact matrixInclusion_entry_outside h M i j (Or.inl (Nat.le_of_not_gt hi))

lemma finProdFinEquiv_cast {n m : ℕ} (h : n ≤ m) (i : Fin n) (r : Fin 2) :
    Fin.castLE (Nat.mul_le_mul_right 2 h) (finProdFinEquiv (i,r)) = finProdFinEquiv (Fin.castLE h i,r) :=
  Fin.ext rfl

theorem matrixInterleave_inclusion {n m : ℕ} (h : n ≤ m) (P : FinMatrix A n × FinMatrix A n) :
    matrixInterleave m (matrixInclusion h P.1,matrixInclusion h P.2) =
      matrixInclusion (Nat.mul_le_mul_right 2 h) (matrixInterleave n P) := by
  apply CStarMatrix.ext; intro i j
  obtain ⟨⟨p,r⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨q,s⟩,rfl⟩ := finProdFinEquiv.surjective j
  by_cases hp : p.val < n
  · by_cases hq : q.val < n
    · let p' : Fin n := ⟨p.val,hp⟩
      let q' : Fin n := ⟨q.val,hq⟩
      have ep : Fin.castLE h p' = p := rfl
      have eq : Fin.castLE h q' = q := rfl
      rw [← ep,← eq,← finProdFinEquiv_cast h,← finProdFinEquiv_cast h,
        matrixInclusion_entry_inside, matrixInterleave_entry]
      rw [finProdFinEquiv_cast h,finProdFinEquiv_cast h,matrixInterleave_entry]
      simp only [matrixInclusion_entry_inside]
    · have hq' : n ≤ q.val := Nat.le_of_not_gt hq
      have hout : n*2 ≤ (finProdFinEquiv (q,s)).val := by
        change n*2 ≤ s.val+2*q.val
        omega
      rw [matrixInclusion_entry_outside _ _ _ _ (Or.inr hout),matrixInterleave_entry]
      simp [matrixInclusion_entry_outside h _ p q (Or.inr hq')]
  · have hp' : n ≤ p.val := Nat.le_of_not_gt hp
    have hout : n*2 ≤ (finProdFinEquiv (p,r)).val := by
      change n*2 ≤ r.val+2*p.val
      omega
    rw [matrixInclusion_entry_outside _ _ _ _ (Or.inl hout),matrixInterleave_entry]
    simp [matrixInclusion_entry_outside h _ p q (Or.inl hp')]

def matrixLimitBlock (n : ℕ) : (FinMatrix A n × FinMatrix A n) →⋆ₙₐ[ℂ] MatrixLimit A :=
  (matrixLimitStage (n*2)).comp (matrixInterleave n)

theorem matrixLimitBlock_norm (n : ℕ) (P : FinMatrix A n × FinMatrix A n) :
    ‖matrixLimitBlock n P‖ = max ‖P.1‖ ‖P.2‖ := by
  change ‖matrixLimitStage (n*2) (matrixInterleave n P)‖ = _
  rw [matrixLimitStage_norm,matrixInterleave_norm]

theorem matrixLimitBlock_compatible {n m : ℕ} (h : n ≤ m) (P : FinMatrix A n × FinMatrix A n) :
    matrixLimitBlock m (matrixInclusion h P.1,matrixInclusion h P.2) = matrixLimitBlock n P := by
  change matrixLimitStage (m*2) (matrixInterleave m _) = matrixLimitStage (n*2) (matrixInterleave n P)
  rw [matrixInterleave_inclusion,matrixLimitStage_compatible]

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
end TraceCone
end

end OAI
