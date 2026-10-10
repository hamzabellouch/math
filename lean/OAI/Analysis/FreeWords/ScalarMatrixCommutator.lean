import Mathlib
import OAI.Analysis.FreeWords.MatrixAveraging
import OAI.Analysis.FreeWords.MatrixHilbertCore

namespace OAI

noncomputable section

namespace KKMatrixHilbert

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scalar_matrix_commutator_bound {n d:ℕ}
    (ρ:Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) (h:H →L[ℂ] H) (δ:ℝ)
    (hδ:∀u:unitary (Matrix (Fin d) (Fin d) ℂ),‖h*ρ u.val-ρ u.val*h‖≤δ)
    (s:unitary (Matrix (Fin n) (Fin n) (H →L[ℂ] H)))
    (hs:∀i j,s.val i j∈ρ.range) :
    ‖matrixOperator (Matrix.diagonal fun _:Fin n => h)*matrixOperator s.val-
      matrixOperator s.val*matrixOperator (Matrix.diagonal fun _:Fin n => h)‖≤2*δ := by
  obtain ⟨h₀,hcomm,hnear⟩ := KKMatrixAveraging.finite_dimensional_commutant_approximation ρ h δ hδ
  let D (a:H →L[ℂ] H) := matrixOperator (Matrix.diagonal fun _:Fin n => a)
  let V : unitary (Amplification n H →L[ℂ] Amplification n H) :=
    ⟨matrixOperator s.val,by
      constructor
      · rw [←matrixOperator_star,←matrixOperator_mul,s.property.1,matrixOperator_one]
      · rw [←matrixOperator_star,←matrixOperator_mul,s.property.2,matrixOperator_one]⟩
  have hd : D h₀*V.val=V.val*D h₀ := by
    change matrixOperator _*matrixOperator _=matrixOperator _*matrixOperator _
    rw [←matrixOperator_mul,←matrixOperator_mul]
    apply congrArg matrixOperator
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
    obtain ⟨a,ha⟩ := hs i j
    rw [←ha]
    exact (hcomm a).eq
  have hsub : D (h-h₀)=D h-D h₀ := by
    ext x i
    simp only [D,matrixOperator_diagonal_apply,sub_apply,PiLp.sub_apply]
  have he : D h*V.val-V.val*D h=D (h-h₀)*V.val-V.val*D (h-h₀) := by
    rw [hsub,sub_mul,mul_sub,hd]
    abel
  change ‖D h*V.val-V.val*D h‖≤2*δ
  rw [he]
  calc
    _ ≤ ‖D (h-h₀)*V.val‖+‖V.val*D (h-h₀)‖ := norm_sub_le _ _
    _ = 2*‖D (h-h₀)‖ := by rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul];ring
    _ ≤ 2*δ := mul_le_mul_of_nonneg_left ((norm_diagonal_le (h-h₀)).trans hnear) (by norm_num)

end

end KKMatrixHilbert
end

end OAI
