import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProductPrior

namespace OAI

/-! Removing the last consecutive constrained block gives exactly the
base/cavity product constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def consecutiveBlockJoin (n K : ℕ) : Spin (K*n+n) ≃ Spin ((K+1)*n) where
  toFun σ := fun i => σ (Fin.cast (Nat.succ_mul K n) i)
  invFun σ := fun i => σ (Fin.cast (Nat.succ_mul K n).symm i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

lemma consecutiveBlockJoin_mem {n K : ℕ} (C : Finset (Spin n)) (σ : Spin (K*n+n)) :
    consecutiveBlockJoin n K σ ∈ consecutiveBlockConstraint n (K+1) C ↔
      σ ∈ cavityProductSlice (consecutiveBlockConstraint n K C) C := by
  rw [mem_consecutiveBlockConstraint, mem_cavityProductSlice, mem_consecutiveBlockConstraint]
  have hl (b : Fin K) :
      (fun i : Fin n => consecutiveBlockJoin n K σ (finProdFinEquiv (b.castSucc,i))) =
        (fun i : Fin n => (cavitySpinSplit (K*n) n σ).1 (finProdFinEquiv (b,i))) := by
    funext i
    apply congrArg σ
    apply Fin.ext
    rfl
  have hr :
      (fun i : Fin n => consecutiveBlockJoin n K σ (finProdFinEquiv (Fin.last K,i))) =
        (cavitySpinSplit (K*n) n σ).2 := by
    funext i
    apply congrArg σ
    apply Fin.ext
    change i.val + n*K = K*n + i.val
    simp [Nat.mul_comm, Nat.add_comm]
  constructor
  · intro h
    exact ⟨fun b => hl b ▸ h b.castSucc, hr ▸ h (Fin.last K)⟩
  · rintro ⟨hlmem,hrmem⟩ b
    refine Fin.lastCases ?_ (fun b => ?_) b
    · rw [hr]
      exact hrmem
    · rw [hl]
      exact hlmem b

lemma consecutiveBlockConstraint_succ {n K : ℕ} (C : Finset (Spin n)) :
    consecutiveBlockConstraint n (K+1) C =
      (cavityProductSlice (consecutiveBlockConstraint n K C) C).map
        (consecutiveBlockJoin n K).toEmbedding := by
  ext σ
  rw [Finset.mem_map]
  constructor
  · intro hσ
    refine ⟨(consecutiveBlockJoin n K).symm σ, ?_, by simp⟩
    exact (consecutiveBlockJoin_mem C _).mp (by simpa using hσ)
  · rintro ⟨τ,hτ,rfl⟩
    exact (consecutiveBlockJoin_mem C τ).mpr hτ

end InvariantIsing

end

end OAI
