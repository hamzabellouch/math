import OAI.Analysis.Laughlin.Fock.SpinRepresentation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem unitary_sum_norm_sq (A : Matrix I I ℂ) (hA : Aᴴ*A=1) (v : I → ℂ) :
    (∑ i, ‖(A *ᵥ v) i‖^2) = ∑ i, ‖v i‖^2 := by
  have h : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,hA,Matrix.vecMul_one]
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self,
    dotProduct,Pi.star_apply,Complex.star_def] using h

theorem unitary_sum_occupationNormSq (Q : ℕ) (A : Matrix I I ℂ) (hA : Aᴴ*A=1)
    (v : I → Space Q) :
    (∑ i, occupationNormSq Q (∑ j, A i j • v j)) = ∑ i, occupationNormSq Q (v i) := by
  simp only [occupationNormSq,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  exact unitary_sum_norm_sq A hA (fun j => (occupationBasis Q).repr (v j) B)

end Laughlin.Fock

end OAI
