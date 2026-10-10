import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.JordanCLM
import OAI.Analysis.MatrixSigning.Potential.Interaction

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def energyMatrix (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (l i*l j/2)*inner ℝ (A i) (jordanCLM X P (A j))

lemma energyMatrix_symm (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d) :
    (energyMatrix A l X P).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,energyMatrix]
  have hh := jordanCLM_symmetric X P (A i) (A j)
  change inner ℝ (jordanCLM X P (A i)) (A j) = inner ℝ (A i) (jordanCLM X P (A j)) at hh
  rw [real_inner_comm (A j) (jordanCLM X P (A i))] at hh
  rw [hh]
  ring

lemma energyMatrix_quad (A : Fin N → H d) (l F : Fin N → ℝ) (X P : H d) :
    F ⬝ᵥ (energyMatrix A l X P *ᵥ F) =
      inner ℝ P (sandwich (responseInput A l F) X) := by
  have hh := jordanCLM_quadratic X P (responseInput A l F)
  have he : inner ℝ (responseInput A l F) (jordanCLM X P (responseInput A l F)) =
      2*(F ⬝ᵥ (energyMatrix A l X P *ᵥ F)) := by
    simp only [responseInput,map_sum,map_smul,sum_inner,inner_sum,
      energyMatrix,Matrix.mulVec,dotProduct,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_left (A j) ((l i*F i) • jordanCLM X P (A i)),
      real_inner_smul_right (A j) (jordanCLM X P (A i))]
    have hj := jordanCLM_symmetric X P (A i) (A j)
    change inner ℝ (jordanCLM X P (A i)) (A j) = inner ℝ (A i) (jordanCLM X P (A j)) at hj
    rw [real_inner_comm (A j) (jordanCLM X P (A i))] at hj
    rw [hj]
    ring
  linarith

lemma energyMatrix_psd (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d)
    (hX : X ∈ psdCone d) (hP : P ∈ psdCone d) : (energyMatrix A l X P).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨energyMatrix_symm A l X P,fun F => ?_⟩
  simp only [star_trivial,energyMatrix_quad]
  exact inner_nonneg_of_psd _ _ hP (sandwich_psd _ _ hX)

lemma energyMatrix_diag (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (i : Fin N) :
    energyMatrix A l X P i i = (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P) := by
  rw [energyMatrix,jordanCLM_quadratic,sandwich_rank_one (A i) X (hA i) (hrank i),
    real_inner_smul_right P (A i),real_inner_comm P (A i)]
  ring

lemma response_energy_cancel (X C : H d) (hX : X ∈ pd d) :
    sandwich (invH X) (sandwich (sandwich X C) (invH X)) = sandwich C X := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)⁻¹*(((X : Mat d)*(C : Mat d)*(X : Mat d))*(X : Mat d)⁻¹*
    ((X : Mat d)*(C : Mat d)*(X : Mat d)))*(X : Mat d)⁻¹ = (C : Mat d)*(X : Mat d)*(C : Mat d)
  simp only [mul_assoc,Matrix.mul_nonsing_inv _ hx,mul_one]
  simp only [← mul_assoc,Matrix.nonsing_inv_mul _ hx,one_mul]

lemma proposed_energy (A : Fin N → H d) (l m F G : Fin N → ℝ) (X Y P Q : H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) :
    energy X Y P Q (sandwich X (responseInput A l F)) (sandwich Y (responseInput A m G)) =
      F ⬝ᵥ (energyMatrix A l X P *ᵥ F)+G ⬝ᵥ (energyMatrix A m Y Q *ᵥ G) := by
  rw [energy,response_energy_cancel X _ hX,response_energy_cancel Y _ hY,
    energyMatrix_quad,energyMatrix_quad]

end
end CurrentKS.Interaction

end OAI
