import OAI.Analysis.FreeEntropy.FisherTestLimit

namespace OAI

universe u1

noncomputable section
open Finset Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem ennreal_sum_iSup_tuple {P : Type u1} [Nonempty P] (n : ℕ) (f : Fin n → P → ℝ≥0∞) :
    (∑i,⨆p,f i p) = ⨆p : Fin n → P,∑i,f i (p i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,ih (fun i => f i.succ),ENNReal.iSup_add]
    simp_rw [ENNReal.add_iSup]
    apply le_antisymm
    · apply iSup_le
      intro a
      apply iSup_le
      intro p
      exact le_iSup_of_le (Fin.cons a p) (by simp [Fin.sum_univ_succ])
    · apply iSup_le
      intro p
      exact le_iSup_of_le (p 0) (le_iSup_of_le (fun i => p i.succ) (by simp [Fin.sum_univ_succ]))
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem fisherTest_zero (i : Fin n) : fisherTest τ X i 0 = 0 := by simp [fisherTest]
 theorem freeFisher_le_liminf_tests {ξ : Fin n → H} (hξ : ConjugateSystem τ X ξ)
    (t : ℕ → Fin n → WordPolynomial n → ℝ) (I : ℕ → ℝ)
    (ht : ∀i p,Tendsto (fun k => t k i p) atTop (𝓝 (fisherTest τ X i p)))
    (hI : ∀k (p : Fin n → WordPolynomial n),∑i,t k i (p i) ≤ I k) :
    freeFisher τ X ≤ liminf (fun k => ENNReal.ofReal (I k)) atTop := by
  rw [freeFisher_variational τ X hξ,ennreal_sum_iSup_tuple]
  apply iSup_le
  intro p
  let q : Fin n → WordPolynomial n := fun i => if 0 ≤ fisherTest τ X i (p i) then p i else 0
  have hq i : 0 ≤ fisherTest τ X i (q i) := by
    dsimp [q]
    split_ifs with h
    · exact h
    · rw [fisherTest_zero]
  have he i : ENNReal.ofReal (fisherTest τ X i (p i)) = ENNReal.ofReal (fisherTest τ X i (q i)) := by
    dsimp [q]
    split_ifs with h
    · rfl
    · rw [fisherTest_zero,ENNReal.ofReal_zero,ENNReal.ofReal_eq_zero]
      exact le_of_not_ge h
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq i)]
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_finsetSum univ (fun i _ => ht i (q i)))
  rw [← ht'.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun k => ENNReal.ofReal_le_ofReal (hI k q)))
end FiniteEntropySeparation

end

end OAI
