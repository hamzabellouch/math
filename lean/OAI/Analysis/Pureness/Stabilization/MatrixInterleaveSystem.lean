import OAI.Analysis.Pureness.Stabilization.MatrixInterleave
import OAI.Analysis.Pureness.Stabilization.MatrixEntries
import OAI.Analysis.Pureness.Stabilization.MatrixLimit

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finProdFinEquiv_cast {n m : ℕ} (h : n ≤ m) (i : Fin n) (r : Fin 2) :
    Fin.castLE (Nat.mul_le_mul_right 2 h) (finProdFinEquiv (i,r)) = finProdFinEquiv (Fin.castLE h i,r) :=
  Fin.ext rfl

omit [PartialOrder A] [StarOrderedRing A] in
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
end CuntzTrace

end

end OAI
