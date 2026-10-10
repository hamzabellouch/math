import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PairVec
import OAI.Analysis.MatrixSigning.Potential.Column

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

local instance rowSquareSumInnerProductSpace : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {m n : ℕ}

lemma row_square_sum (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    (∑ j, C i j ^ 2) = (C*C.conjTranspose) i i := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,sq]

lemma sqrt_mul_transpose {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    CFC.sqrt Γ*(CFC.sqrt Γ).conjTranspose = Γ := by
  rw [(CFC.sqrt_nonneg Γ).posSemidef.isHermitian.eq,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg]

lemma rectangular_row_moments (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m}
    (hΓ : Γ.PosSemidef) (i : Fin n) :
    (∑ j, (R.toEuclideanLin (column (CFC.sqrt Γ) j) i)^2) = (R*Γ*R.conjTranspose) i i := by
  have he : R*(CFC.sqrt Γ)*(R*(CFC.sqrt Γ)).conjTranspose = R*Γ*R.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = R*(CFC.sqrt Γ*(CFC.sqrt Γ).conjTranspose)*R.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_mul_transpose hΓ]
  rw [← he,← row_square_sum]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma diagonal_bound_to_scalar {Γ : Mat m} (hΓ : Γ.PosSemidef)
    (hd : ∀ i, Γ i i ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ) (hs : (slack κ Γ).PosSemidef) :
    (κ • (1 : Mat m)-Γ).PosSemidef := by
  have hh : (1-Matrix.diagonal (Matrix.diag Γ) : Mat m).PosSemidef := by
    rw [← Matrix.diagonal_one,Matrix.diagonal_sub,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (hd i)
  have hp := (hh.smul hκ).add hs
  refine ⟨(Matrix.isHermitian_one.smul (IsSelfAdjoint.of_nonneg hκ)).sub hΓ.isHermitian, ?_⟩
  have decomposition : κ • (1 : Mat m)-Γ =
      κ • (1-Matrix.diagonal (Matrix.diag Γ)) + slack κ Γ := by
    unfold slack
    module
  rw [decomposition]
  exact hp.2

lemma response_row_bound (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m} {κ : ℝ}
    (hΓ : Γ.PosSemidef) (hbound : (κ • (1 : Mat m)-Γ).PosSemidef) (i : Fin n) :
    (∑ j, (R.toEuclideanLin (column (CFC.sqrt Γ) j) i)^2) ≤ κ*(∑ j, R i j^2) := by
  rw [rectangular_row_moments R hΓ,row_square_sum]
  have hh := (hbound.mul_mul_conjTranspose_same R).diag_nonneg (i := i)
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one] at hh
  change 0 ≤ κ*(R*R.conjTranspose) i i-(R*Γ*R.conjTranspose) i i at hh
  exact sub_nonneg.mp hh

lemma rectangular_total_movement (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m}
    (hΓ : Γ.PosSemidef) :
    (∑ j, ‖R.toEuclideanLin (column (CFC.sqrt Γ) j)‖^2) = (R*Γ*R.conjTranspose).trace := by
  simp_rw [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => rectangular_row_moments R hΓ i

lemma movement_lower_bound (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m}
    (hΓ : Γ.PosSemidef) {E0 b : ℝ} (htr : b ≤ Γ.trace)
    (hresponse : ∀ x, ‖Γ.toEuclideanLin x‖^2 ≤ E0*‖R.toEuclideanLin (Γ.toEuclideanLin x)‖^2) :
    b ≤ E0*(∑ j, ‖R.toEuclideanLin (column (CFC.sqrt Γ) j)‖^2) := by
  calc
    b ≤ Γ.trace := htr
    _ = ∑ j, ‖column (CFC.sqrt Γ) j‖^2 := (total_movement hΓ).symm
    _ ≤ ∑ j, E0*‖R.toEuclideanLin (column (CFC.sqrt Γ) j)‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact sqrt_column_range hΓ (fun x => ‖x‖^2 ≤ E0*‖R.toEuclideanLin x‖^2) hresponse j
    _ = _ := (Finset.mul_sum _ _ _).symm

end

open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

local instance rowSquareSumWeightedInnerProductSpace : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {n : ℕ}

lemma weighted_column_moments (D : Fin (2*n) → ℝ) (hD : ∀ i, 0 < D i) {Γ : Mat (2*n)}
    (hΓ : Γ.PosSemidef) :
    (∑ j, ‖weightEquiv D hD (column (CFC.sqrt Γ) j)‖^2) = ∑ i,D i*Γ i i := by
  simp_rw [weight_norm_sq]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,row_moments hΓ]

lemma weighted_energy_moments (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (B : Mat n) (Q Γ : Mat (2*n)) (hQ : Q.PosSemidef) (hΓ : Γ.PosSemidef)
    (hdiag : ∀ i, Q i i = pairWeight a b i)
    (hslack : (slack 4 Γ).PosSemidef)
    (hrange : ∀ x, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (Γ.toEuclideanLin x)‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B (Γ.toEuclideanLin x) i)^2)) :
    (∑ j, quad Q (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
  rw [sqrt_moments hΓ]
  have hd := energy_trace_domination Q Γ hQ hslack
  simp only [hdiag] at hd
  rw [← weighted_column_moments (pairWeight a b) (pairWeight_pos a b ha hb) hΓ] at hd
  have hw : (∑ j, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (column (CFC.sqrt Γ) j)‖^2) ≤
      ∑ j,4*(∑ i,(a i+b i)*(responseLin B (column (CFC.sqrt Γ) j) i)^2) := by
    apply Finset.sum_le_sum
    intro j _
    exact sqrt_column_range hΓ (fun v => ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B v i)^2)) hrange j
  have he : (∑ j,4*(∑ i,(a i+b i)*(responseLin B (column (CFC.sqrt Γ) j) i)^2)) =
      4*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [he] at hw
  linarith

theorem weighted_block_ensemble (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (Q : Mat (2*n)) (hQ : Q.PosSemidef) (hdiag : ∀ i, Q i i = pairWeight a b i)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧ (∀ i, Γ i i ≤ 1) ∧
      ((4 : ℝ) • (1 : Mat (2*n))-Γ).PosSemidef ∧ (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ j, constraintLin A B (column (CFC.sqrt Γ) j) = 0) ∧
      (∑ j, quad Q (column (CFC.sqrt Γ) j)) ≤
        16*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
  obtain ⟨Γ,hΓ,hd,hs,ht,hL,hc⟩ := weighted_block_covariance a b ha hb A B (constraintLin A B) hA hB
  refine ⟨Γ,hΓ,hd,diagonal_bound_to_scalar hΓ hd (by norm_num) hs,ht,?_,?_⟩
  · intro j
    exact sqrt_column_range hΓ (fun v => constraintLin A B v = 0) hL j
  · exact weighted_energy_moments a b ha hb B Q Γ hQ hΓ hdiag hs
      (fun x => weighted_response_bound a b ha hb A B _ (hL x) (hc x))

end CurrentKS.Covariance

end

end OAI
