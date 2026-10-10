import OAI.Analysis.Quantum.PPTSquare.QuadraticCriterion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ExplicitPencil
open ChannelCompletion TensorCriterion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def M (i : Fin 4) : Matrix (Fin 6) (Fin 4) ℂ := (data i).map (Int.castRingHom ℂ)

def pencil (x : Fin 4 → ℂ) : Matrix (Fin 6) (Fin 4) ℂ := ∑ i, x i • M i

def L : Map (Fin 4) (Fin 4) where
  toFun A := ∑ i, ∑ j, A i j • ((M i)ᵀ * M j)
  map_add' A B := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c A := by simp [smul_smul, Finset.smul_sum]

open ChannelCompletion TensorCriterion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

lemma data_symmetry : ∀ i j : Fin 4, (data i)ᵀ * data j = (data j)ᵀ * data i := by decide

lemma M_real (i : Fin 4) : (M i)ᴴ = (M i)ᵀ := by
  ext a b
  simp [M, Matrix.conjTranspose_apply]

lemma M_symmetry (i j : Fin 4) : (M i)ᵀ * M j = (M j)ᵀ * M i := by
  have hh := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ => A.map (Int.castRingHom ℂ))
    (data_symmetry i j)
  simpa only [M, Matrix.map_mul, Matrix.transpose_map] using hh

@[simp] lemma L_apply (A : Mat (Fin 4)) : L A = ∑ i, ∑ j, A i j • ((M i)ᵀ * M j) := rfl

@[simp] lemma L_single (i j : Fin 4) : L (Matrix.single i j 1) = (M i)ᵀ * M j := by
  simp [L_apply, Matrix.single_apply, ite_and]

def kraus (r : Fin 6) : Mat (Fin 4) := Matrix.of fun a i => M i r a

lemma kraus_entry (i j : Fin 4) (a b : Fin 4) :
    ((M i)ᵀ * M j) a b = ∑ r, kraus r a i * star (kraus r b j) := by
  simp [Matrix.mul_apply, kraus, M]

lemma L_eq_kraus : L = ∑ r, ad (kraus r) := by
  apply LinearMap.ext
  intro A
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A B hA hB => simp only [map_add, hA, hB]
  | h_std_basis i j c =>
    have hc : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by simp
    rw [hc, map_smul, map_smul]
    congr 1
    ext a b
    simp only [L_single, LinearMap.sum_apply, Matrix.sum_apply, ad_single_apply]
    exact kraus_entry i j a b

lemma L_cp : CP L := by rw [L_eq_kraus]; exact cp_sum _ (fun r => cp_ad _)

lemma transpose_L : transposeMap.comp L = L := by
  apply LinearMap.ext
  intro A
  change (L A)ᵀ = L A
  simp only [L_apply, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [M_symmetry]

lemma L_ppt : PPT L := by
  refine ⟨L_cp, ?_⟩
  rw [transpose_L]
  exact L_cp

end ExplicitPencil

end

end OAI
