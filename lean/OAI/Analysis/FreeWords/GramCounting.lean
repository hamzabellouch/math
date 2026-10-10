import Mathlib
import OAI.Analysis.FreeWords.PermutationDistance
import OAI.Analysis.FreeWords.TensorGram

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

theorem permutationGram_count {r d : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationGram r d π σ=(d : ℂ)^Fintype.card (Quotient (matchingSetoid π σ)) := by
  classical
  rw [permutationGram_apply,matrixPair_apply]
  have he (a : Fin r → Fin d) :
      (∑ b,star (positionMatrix π a b)*positionMatrix σ a b)=
      if a ∘ π=a ∘ σ then (1 : ℂ) else 0 := by
    simp [positionMatrix,eq_comm]
  simp_rw [he]
  have hc := Fintype.card_congr (matchingEquiv (β := Fin d) π σ)
  rw [Fintype.card_fun,Fintype.card_fin] at hc
  rw [← Nat.cast_pow,← hc]
  simp [Fintype.card_subtype]

theorem permutationGram_distance {r d : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationGram r d π σ=(d : ℂ)^(r-permutationDistance π σ) := by
  rw [permutationGram_count]
  congr 1
  have h := permutationDistance_add_classes π σ
  omega

def distanceMatrix {ι : Type*} (δ : ι → ι → ℕ) (t : ℝ) : Matrix ι ι ℂ :=
  fun i j => (t : ℂ)^(δ i j)

theorem permutationGram_scalar_distance {r d : ℕ} (hd : 0 < d) :
    permutationGram r d=(d : ℂ)^r • distanceMatrix permutationDistance (d : ℝ)⁻¹ := by
  ext π σ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := permutationDistance_add_classes π σ
  simp only [Matrix.smul_apply,smul_eq_mul,distanceMatrix,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [permutationGram_count]
  conv_rhs => lhs; rw [← h,pow_add]
  simp [inv_pow,mul_comm,hd0]

end

end KKWeingarten
end

end OAI
