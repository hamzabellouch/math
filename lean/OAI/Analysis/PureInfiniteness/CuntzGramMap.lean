import OAI.Analysis.WeakInfiniteness.NuclearCoefficients
import OAI.Analysis.Nuclearity.UnitalCPContraction

namespace OAI

/-! # Finite matrix return maps from Cuntz families

Conjugating the matrix corner associated to orthogonal isometries realizes
the Gram-coefficient maps used by the finite Fock approximation.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

def cuntzMatrixLinear (r : n → A) : CStarMatrix n n ℂ →ₗ[ℂ] A :=
  ∑ i, ∑ j, (matrixEntryLinear i j).smulRight (r i * star (r j))

omit [DecidableEq n] in
@[simp] lemma cuntzMatrixLinear_apply (r : n → A) (M : CStarMatrix n n ℂ) :
    cuntzMatrixLinear r M = ∑ i, ∑ j, M i j • (r i * star (r j)) := by
  simp only [cuntzMatrixLinear, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

omit [Fintype n] in
private lemma cuntzMatrix_term_mul (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (M N : CStarMatrix n n ℂ) (i j k l : n) :
    (M i j • (r i * star (r j))) * (N k l • (r k * star (r l))) =
      if j = k then (M i j * N k l) • (r i * star (r l)) else 0 := by
  rw [smul_mul_smul_comm]
  have h : (r i * star (r j)) * (r k * star (r l)) =
      r i * (star (r j) * r k) * star (r l) := by noncomm_ring
  rw [h, hr]
  split_ifs <;> simp

def cuntzMatrixHom (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0) :
    CStarMatrix n n ℂ →⋆ₙₐ[ℂ] A where
  toFun := cuntzMatrixLinear r
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' M N := by
    rw [cuntzMatrixLinear_apply, cuntzMatrixLinear_apply, cuntzMatrixLinear_apply]
    simp only [CStarMatrix.mul_apply, Finset.sum_smul]
    simp only [Finset.sum_mul, Finset.mul_sum,
      cuntzMatrix_term_mul r hr, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    calc
      _ = ∑ i, ∑ k, ∑ j, (M i k * N k j) • (r i * star (r j)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (M i k * N k j) • (r i * star (r j)) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
  map_star' M := by
    simp only [cuntzMatrixLinear_apply, CStarMatrix.star_apply, star_sum,
      star_smul, star_mul, star_star]
    exact Finset.sum_comm

@[simp] lemma cuntzMatrixHom_apply (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0) (M : CStarMatrix n n ℂ) :
    cuntzMatrixHom r hr M = ∑ i, ∑ j, M i j • (r i * star (r j)) :=
  cuntzMatrixLinear_apply r M

def cuntzGramMap (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0) (v : n → A) :
    CStarMatrix n n ℂ →L[ℂ] A :=
  (ContinuousLinearMap.mulLeftRight ℂ A (star (∑ i, r i * v i)) (∑ i, r i * v i)).comp
    (starHomContinuousLinear (cuntzMatrixHom r hr))

lemma cuntzGramMap_apply (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (v : n → A) (M : CStarMatrix n n ℂ) :
    cuntzGramMap r hr v M = ∑ i, ∑ j, M i j • (star (v i) * v j) := by
  have hl (i : n) : star (∑ k, r k * v k) * r i = star (v i) := by
    simp only [star_sum, Finset.sum_mul, star_mul]
    have he (k : n) : (star (v k) * star (r k)) * r i =
        if k = i then star (v k) else 0 := by
      rw [mul_assoc, hr]; split_ifs <;> simp
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hh (j : n) : star (r j) * (∑ k, r k * v k) = v j := by
    simp only [Finset.mul_sum, ← mul_assoc, hr]
    simp
  have hterm (i j : n) :
      star (∑ k, r k * v k) * (M i j • (r i * star (r j))) *
        (∑ k, r k * v k) = M i j • (star (v i) * v j) := by
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    calc
      _ = (star (∑ k, r k * v k) * r i) *
          (star (r j) * (∑ k, r k * v k)) := by noncomm_ring
      _ = _ := by rw [hl, hh]
  change star (∑ i, r i * v i) * (cuntzMatrixHom r hr M) * (∑ i, r i * v i) = _
  rw [cuntzMatrixHom_apply]
  calc
    _ = ∑ i, ∑ j, star (∑ k, r k * v k) *
        (M i j • (r i * star (r j))) * (∑ k, r k * v k) := by
      conv_lhs => arg 1; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => arg 1; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
    _ = _ := by simp only [hterm]

@[simp] lemma cuntzGramMap_one (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0) (v : n → A) :
    cuntzGramMap r hr v 1 = ∑ i, star (v i) * v i := by
  rw [cuntzGramMap_apply]
  simp [CStarMatrix.one_apply]

variable [PartialOrder A] [StarOrderedRing A]

lemma cuntzGramMap_cp (r : n → A)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0) (v : n → A) :
    CompletelyPositive (cuntzGramMap r hr v) := by
  intro k X hX
  let D := matrixDiagonalHom (n := Fin k) (∑ i, r i * v i)
  have hY := star_left_conjugate_nonneg
    (map_nonneg (CStarMatrix.mapₙₐ (cuntzMatrixHom r hr)) hX) D
  convert hY using 1
  ext i j
  have hD (i j : Fin k) : D i j = if i = j then ∑ i, r i * v i else 0 := rfl
  have hsD (i j : Fin k) : star D i j =
      if j = i then star (∑ i, r i * v i) else 0 := by
    rw [CStarMatrix.star_apply, hD]
    split_ifs <;> simp
  change star (∑ i, r i * v i) * (cuntzMatrixHom r hr (X i j)) *
    (∑ i, r i * v i) = _
  simp [CStarMatrix.mul_apply, hsD, hD]

end WeakPureInfiniteness

end

end OAI
