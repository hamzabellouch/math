import OAI.Analysis.Mahler.StripDifferential
import OAI.Analysis.Mahler.Jacobian
import Mathlib.LinearAlgebra.Determinant

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix
open MahlerConformal
variable {n N : ℕ}

/-- Determinant of a real linear map that fixes its first coordinate and has
vertical block G; arbitrary mixed derivatives do not affect the determinant. -/
lemma det_eq_vertical_block
    (L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)))
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hfst : ∀ z, (L z).1 = z.1)
    (hvertical : ∀ y, (L (0,y)).2 = G.mulVec y) : L.det = G.det := by
  let b := (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => (L (Pi.single j 1,0)).2 i
  have he : LinearMap.toMatrix b b L = Matrix.fromBlocks 1 0 C G := by
    ext (i | i) (j | j) <;>
      simp [b,C,LinearMap.toMatrix_apply,Module.Basis.prod_apply,Pi.basisFun_apply,hfst,hvertical,
        Matrix.fromBlocks,Matrix.one_apply,Pi.single_apply]
  rw [← LinearMap.det_toMatrix b,he,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,one_mul]

lemma stripDerivative_fst (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) : (stripDerivative A m z w).1 = w.1 := rfl

lemma stripDerivative_vertical (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) (y : Fin n → ℝ) :
    (stripDerivative A m z (0,y)).2 =
      (weightedGram A (fun j => planarDensity m (stripCoordinate A z j))).mulVec y := by
  funext i
  have hcoord : ∀ j, stripCoordinateCLM A j (0,y) = measurement A y j • (I : ℂ) := by
    intro j
    simp [stripCoordinateCLM_apply,stripCoordinate,measurement,Complex.real_smul]
  have hP : ∀ j, planarDifferential m (stripCoordinate A z j) I =
      planarDensity m (stripCoordinate A z j) := fun j => planarDifferential_I m (hz j)
  simp only [stripDerivative,ContinuousLinearMap.prod_apply,ContinuousLinearMap.pi_apply,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    hcoord,map_smul,hP,smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, weightedGram_apply,measurement,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact Jacobian identity for the actual derivative of the actual map. -/
theorem abs_det_stripDerivative (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) :
    |(stripDerivative A m z).det| = (4/(Real.pi*(m : ℝ)))^n*
      (weightedGram A (fun j => hessianWeight m (inverseF (stripCoordinate A z j))
        (deriv inverseF (stripCoordinate A z j)))).det := by
  have hdet := det_eq_vertical_block (stripDerivative A m z).toLinearMap
    (weightedGram A (fun j => planarDensity m (stripCoordinate A z j)))
    (stripDerivative_fst A m z) (stripDerivative_vertical A m hz)
  change |(stripDerivative A m z).toLinearMap.det| = _
  rw [hdet]
  have hw : (fun j => planarDensity m (stripCoordinate A z j)) =
      fun j => (4/(Real.pi*(m : ℝ)))*hessianWeight m (inverseF (stripCoordinate A z j))
        (deriv inverseF (stripCoordinate A z j)) := by
    funext j
    rw [planarDensity_eq m (by omega)]
    exact verticalWeight_eq_scaled_hessianWeight (by exact_mod_cast (show m ≠ 0 by omega)) _ _
  rw [hw,weightedGram_smul,Matrix.det_smul,Fintype.card_fin]
  apply abs_of_nonneg
  exact mul_nonneg (pow_nonneg (by positivity) _) (weightedGram_det_nonneg A
    (fun j => hessianWeight_nonneg _ _ _))

end SymmetricMahler

end OAI
