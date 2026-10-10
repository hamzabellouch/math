import OAI.Probability.SignedSweeps.HilbertBlockNorm
import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I E F : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem hilbertBlock_sum_lower (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j)
    (T : F →ₗ[ℂ] F) (hT : T.IsPositive)
    (A P : I → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsSymmetric)
    (hTA : ∀ i, T ∘ₗ (j i).toLinearMap = (j i).toLinearMap ∘ₗ A i)
    (c : ℂ) (hlower : ∀ i, (A i - c • P i).IsPositive) :
    (T - c • ∑ i, hilbertBlock (j i) (P i)).IsPositive := by
  let K := ∑ i, hilbertBlock (j i) 1
  have hK : K.IsSymmetric := LinearMap.isSymmetric_sum _
    (fun _ _ => hilbertBlock_symmetric _ LinearMap.IsSymmetric.one)
  have hKK : K * K = K := by
    dsimp only [K]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · exact hilbertBlock_idempotent _ (one_mul _)
    · intro k _ hki
      exact hilbertBlock_orthogonal _ _ (hj hki.symm) 1 1
    · simp
  have hcomm_i (i : I) : T * hilbertBlock (j i) 1 = hilbertBlock (j i) 1 * T := by
    apply hilbertBlock_intertwine _ _ (A i) 1 (hTA i)
    · rw [hT.isSymmetric.adjoint_eq, (hA i).adjoint_eq]
      exact hTA i
    · simp
  have hKT : K * T = T * K := by
    dsimp only [K]
    simp only [Finset.sum_mul, Finset.mul_sum, hcomm_i]
  have hright : K * T = ∑ i, hilbertBlock (j i) (A i) := by
    rw [hKT]
    dsimp only [K]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hilbertBlock_left_intertwine _ _ _ _ (hTA i), mul_one]
  have hR : (1 - K).IsSymmetric := LinearMap.IsSymmetric.one.sub hK
  have hRR : (1 - K) * (1 - K) = 1 - K := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hKK]
    abel
  have hRT : (1 - K) * T = T * (1 - K) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hKT]
  have hres := positive_commuting_projection T (1 - K) hT hR hRR hRT
  have hsum : (∑ i, hilbertBlock (j i) (A i - c • P i)).IsPositive :=
    LinearMap.isPositive_sum _ (fun i _ => hilbertBlock_positive _ (hlower i))
  have hs : ∑ i, hilbertBlock (j i) (A i - c • P i) =
      K * T - c • ∑ i, hilbertBlock (j i) (P i) := by
    rw [hright]
    simp only [map_sub, map_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have he : T - c • ∑ i, hilbertBlock (j i) (P i) =
      (1 - K) * T + ∑ i, hilbertBlock (j i) (A i - c • P i) := by
    rw [hs, sub_mul, one_mul]
    abel
  rw [he]
  exact hres.add hsum

theorem tensor_map_lower (A P : E →ₗ[ℂ] E) (B Q : F →ₗ[ℂ] F)
    (hP : P.IsPositive) (hB : B.IsPositive)
    (a b : ℝ) (ha : 0 ≤ a)
    (hA : (A - (a : ℂ) • P).IsPositive)
    (hB' : (B - (b : ℂ) • Q).IsPositive) :
    (TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q).IsPositive := by
  have h₁ := tensor_map_positive _ B hA hB
  have h₂ := tensor_map_positive _ _ (hP.smul_of_nonneg (Complex.zero_le_real.mpr ha)) hB'
  have he : TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q =
      TensorProduct.map (A - (a : ℂ) • P) B +
        TensorProduct.map ((a : ℂ) • P) (B - (b : ℂ) • Q) := by
    apply TensorProduct.ext
    ext x y
    change (TensorProduct.map A B - ((a * b : ℝ) : ℂ) • TensorProduct.map P Q) (x ⊗ₜ[ℂ] y) =
      (TensorProduct.map (A - (a : ℂ) • P) B +
        TensorProduct.map ((a : ℂ) • P) (B - (b : ℂ) • Q)) (x ⊗ₜ[ℂ] y)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Complex.ofReal_mul]
    simp only [mul_comm (b : ℂ) (a : ℂ)]
    abel
  rw [he]
  exact h₁.add h₂

end SignedSweeps
end

end OAI
