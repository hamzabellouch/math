import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKMatrixQuantization

noncomputable section

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrixHom_trace (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℂ] ℂ)
    (h1 : τ 1=1) (htr : ∀ x y, τ (x*y)=τ (y*x)) (x : Matrix ι ι ℂ) :
    τ (ρ x)=(Fintype.card ι:ℂ)⁻¹*Matrix.trace x := by
  classical
  let o : ι := Classical.choice inferInstance
  have he (i j : ι) : τ (matrixUnit ρ i j)=if i=j then τ (matrixUnit ρ o o) else 0 := by
    by_cases hij : i=j
    · subst j
      have hh := htr (matrixUnit ρ i o) (matrixUnit ρ o i)
      simpa only [matrixUnit_mul,ite_true] using hh
    · have hh := htr (matrixUnit ρ i i) (matrixUnit ρ i j)
      simpa only [matrixUnit_mul,ite_true,ite_eq_right hij,ite_eq_right (Ne.symm hij),map_zero] using hh
  have hd (i : ι) : τ (matrixUnit ρ i i)=τ (matrixUnit ρ o o) := by
    have hh := he i i
    simpa only [ite_true] using hh
  have hs : (Fintype.card ι:ℂ)*τ (matrixUnit ρ o o)=1 := by
    calc
      (Fintype.card ι:ℂ)*τ (matrixUnit ρ o o) = ∑ i : ι, τ (matrixUnit ρ o o) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ∑ i : ι, τ (matrixUnit ρ i i) := Finset.sum_congr rfl (fun i _ => (hd i).symm)
      _ = τ (∑ i : ι, matrixUnit ρ i i) := (map_sum τ _ _).symm
      _ = 1 := by rw [matrixUnit_sum_diag,h1]
  have hc : (Fintype.card ι:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  have ho : τ (matrixUnit ρ o o)=(Fintype.card ι:ℂ)⁻¹ := by
    apply mul_left_cancel₀ hc
    rw [hs,mul_inv_cancel₀ hc]
  have he' (i j : ι) : τ (matrixUnit ρ i j)=if i=j then (Fintype.card ι:ℂ)⁻¹ else 0 := by
    rw [he i j,ho]
  rw [matrix_representation]
  simp only [map_sum,map_smul,he',smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true,Matrix.trace,Matrix.diag,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end

end KKVariableUltra
end

end OAI
