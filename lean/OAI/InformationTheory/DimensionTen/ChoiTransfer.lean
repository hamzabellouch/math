import OAI.Analysis.Quantum.DimensionTen.Main
import OAI.InformationTheory.SecretKey.Main

namespace OAI

/-! Transpose-adjoint transfer for the explicit dimension-ten maps. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped ComplexOrder Kronecker ENNReal

namespace DimensionTen
universe u

lemma operational_matrixUnit {a : ℕ} (i j : Fin a) :
    ZeroKey.matrixUnit i j = Matrix.single i j (1 : ℂ) := by
  ext u v
  simp [ZeroKey.matrixUnit, Matrix.single_apply, ite_and, eq_comm]

def phiOneSharp : Mat 10 →ₗ[ℂ] Mat 10 :=
  asLinearMap (krausMap (fun p => (phiOneKraus p)ᵀ)) (krausMap_linear _)

def phiTwoLinear : Mat 10 →ₗ[ℂ] Mat 10 := asLinearMap phiTwo phiTwo_ppt.1

lemma phiOneSharp_single (x y i j : Fin 10) :
    phiOneSharp (Matrix.single x y 1) i j = phiOne (Matrix.single i j 1) x y := by
  change krausMap (fun p : Fin 6 × Fin 6 => (phiOneKraus p)ᵀ)
    (Matrix.single x y 1) i j = _
  rw [phiOne_kraus, krausMap_single, krausMap_single]
  rfl

lemma phiOneSharp_apply (A : Mat 10) (i j : Fin 10) :
    phiOneSharp A i j =
      ∑ x, ∑ y, A x y * phiOne (Matrix.single i j 1) x y := by
  conv_lhs => rw [matrix_expansion A]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, phiOneSharp_single]

lemma phiOneSharp_input_transpose (A : Mat 10) : phiOneSharp Aᵀ = phiOneSharp A := by
  ext i j
  simp only [phiOneSharp_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have he := congrArg (fun B : Mat 10 => B x y) (phiOne_output_transpose (Matrix.single i j 1))
  change phiOne (Matrix.single i j 1) y x = phiOne (Matrix.single i j 1) x y at he
  rw [he]

lemma hsAdjoint_input_transpose {a b : ℕ} (F : Mat a → Mat b)
    (h : ∀ A, (F A)ᵀ = F A) (Y : Mat b) :
    hsAdjoint F Yᵀ = hsAdjoint F Y := by
  ext i j
  simp only [hsAdjoint, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have he := congrArg (fun B : Mat b => B u v) (h (Matrix.single i j 1))
  change F (Matrix.single i j 1) v u = F (Matrix.single i j 1) u v at he
  rw [he]

lemma phiTwo_input_transpose (A : Mat 10) : phiTwo Aᵀ = phiTwo A := by
  unfold phiTwo
  rw [← real_compression_transpose _ firstSix_real,
    hsAdjoint_input_transpose _ complementaryMap_output_transpose]

lemma phiOneSharp_pptType : ZeroKey.PPTType phiOneSharp := by
  have hcp : ZeroKey.CompletelyPositive phiOneSharp :=
    ZeroKey.cp_of_kraus_representation phiOneSharp (fun p => (phiOneKraus p)ᵀ)
      (fun _ => rfl)
  refine ⟨hcp, ?_⟩
  have he : phiOneSharp.comp (ZeroKey.transposeLinear 10) = phiOneSharp := by
    ext A i j
    exact congrArg (fun B : Mat 10 => B i j) (phiOneSharp_input_transpose A)
  rw [he]
  exact hcp

lemma phiTwo_pptType : ZeroKey.PPTType phiTwoLinear := by
  have hcp : ZeroKey.CompletelyPositive phiTwoLinear := by
    apply ZeroKey.cp_of_kraus_representation phiTwoLinear phiTwoKraus
    intro A
    change phiTwo A = _
    rw [phiTwo_kraus]
    rfl
  refine ⟨hcp, ?_⟩
  have he : phiTwoLinear.comp (ZeroKey.transposeLinear 10) = phiTwoLinear := by
    ext A i j
    exact congrArg (fun B : Mat 10 => B i j) (phiTwo_input_transpose A)
  rw [he]
  exact hcp

lemma compositeChoi_transfer :
    ZeroKey.tensorMap phiOneSharp phiTwoLinear (ZeroKey.outer (omega 10) (omega 10)) =
      compositeChoi := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [ZeroKey.tensorMap, ZeroKey.outer, omega, operational_matrixUnit,
    phiOneSharp_single]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ x, ∑ y, phiOne (Matrix.single i j 1) x y * phiTwo (Matrix.single x y 1) u v) =
    phiTwo (phiOne (Matrix.single i j 1)) u v
  conv_rhs => rw [linear_expansion phiTwo phiTwo_ppt.1]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end DimensionTen

end

end OAI
