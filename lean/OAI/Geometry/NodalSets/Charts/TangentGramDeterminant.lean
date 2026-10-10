import Mathlib.Data.Matrix.ColumnRowPartitioned
import OAI.Geometry.NodalSets.Elliptic.RadialVolumeMatrix

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

lemma rectangular_congruence_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : n ≃ m)
    (R : Matrix m m ℝ) (F : Matrix m n ℝ) :
    (F.transpose * R * F).det = R.det * (F.transpose * F).det := by
  let G := F.submatrix e id
  have h : G.transpose * R.submatrix e e * G = F.transpose * R * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  have h0 : G.transpose * G = F.transpose * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  rw [← h,← h0]
  simp only [det_mul,det_transpose,det_submatrix_equiv_self]
  ring

lemma augmented_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] [Unique k]
    (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    ((fromCols J (replicateCol k x)).transpose * R *
      fromCols J (replicateCol k x)).det = (J.transpose * R * J).det := by
  rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols]
  have ht : J.transpose * R * replicateCol k x = 0 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx,← replicateCol_mulVec,hJ]
    rfl
  have hb : (replicateCol k x).transpose * R * replicateCol k x = 1 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx]
    ext i j
    simpa [mul_apply,replicateCol,dotProduct,Matrix.one_apply,Subsingleton.elim i j] using hn
  rw [ht,hb,det_fromBlocks_zero₁₂,det_one,mul_one]

lemma tangent_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] [Unique k]
    (e : (n ⊕ k) ≃ m) (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * R * J).det = R.det * (J.transpose * J).det := by
  have h := rectangular_congruence_det e R (fromCols J (replicateCol k x))
  rw [augmented_gram_det R J x hx hn hJ] at h
  have h0 := augmented_gram_det (k := k) (1 : Matrix m m ℝ) J x
    (one_mulVec x) hn hJ
  simp only [Matrix.mul_one] at h0
  rwa [h0] at h

local instance : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
local instance : Fintype (Fin 1) := Unique.fintype

lemma radial_tangent_gram_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ) (J : Matrix (Fin 5) (Fin 4) ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * weightedBaseMatrix A rho * J).det =
      (rho^4 / A.det) * (J.transpose * J).det := by
  have hcol (j : Fin 4) : x ⬝ᵥ (fun i ↦ J i j) = 0 := by
    have h := congrFun hJ j
    simpa only [mulVec,transpose_apply,Pi.zero_apply,dotProduct_comm] using h
  have he : radialVolumeMatrix A rho x * J = weightedBaseMatrix A rho * J := by
    ext i j
    exact congrFun (radialVolumeMatrix_tangent A rho x (fun i ↦ J i j) (hcol j)) i
  have h := tangent_gram_det (finSumFinEquiv : (Fin 4 ⊕ Fin 1) ≃ Fin 5)
    (radialVolumeMatrix A rho x) J x (radialVolumeMatrix_radial A hA rho x hx hn) hn hJ
  rw [radialVolumeMatrix_det A hA hr x hx hn,Matrix.mul_assoc,he,← Matrix.mul_assoc] at h
  exact h

end
end Yau.Geometry

end OAI
