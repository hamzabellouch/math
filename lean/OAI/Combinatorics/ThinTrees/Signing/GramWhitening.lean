import Mathlib
import OAI.Combinatorics.ThinTrees.RationalMatrix.Gram
import OAI.Combinatorics.ThinTrees.RationalMatrix.Inverse

namespace OAI

/-! Gram whitening. -/

section

namespace AlgorithmicThinTrees.GramWhitening
open Matrix Finset
open scoped MatrixOrder
variable {n d m : ℕ}

lemma congruence_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B)
    (R : Matrix (Fin n) (Fin d) ℝ) : Rᵀ*A*R ≤ Rᵀ*B*R := by
  rw [Matrix.le_iff]
  have hh := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same R
  simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul] using hh

lemma symmetric_of_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) : Aᵀ=A :=
  (isHermitian_iff_isSymm.mp hA.isHermitian).eq

lemma projection_le_one {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Qᵀ=Q) (hQQ : Q*Q=Q) : Q ≤ 1 := by
  rw [Matrix.le_iff]
  have hh := posSemidef_conjTranspose_mul_self (1-Q)
  rw [conjTranspose_eq_transpose_of_trivial] at hh
  have he : (1-Q)ᵀ*(1-Q) = 1-Q := by
    rw [transpose_sub,transpose_one,hQ,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.one_mul,Matrix.one_mul,Matrix.mul_one,hQQ]
    abel
  rwa [he] at hh

lemma normalized_covariance (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹) :
    Rᵀ*P*R ≤ 1 := by
  have hPP : P⁻¹*P=1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hP.isUnit)
  apply projection_le_one
  · rw [transpose_mul,transpose_mul,transpose_transpose,symmetric_of_psd hP.posSemidef]
    simp only [Matrix.mul_assoc]
  · calc
      Rᵀ*P*R*(Rᵀ*P*R) = Rᵀ*P*(R*Rᵀ)*P*R := by simp only [Matrix.mul_assoc]
      _ = Rᵀ*P*R := by rw [hRR,Matrix.mul_assoc (Rᵀ*P) P⁻¹ P,hPP,Matrix.mul_one]

lemma rectangular_norm (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    (Rᵀ*ᵥb) ⬝ᵥ (Rᵀ*ᵥb)=b ⬝ᵥ ((R*Rᵀ)*ᵥb) := by
  rw [dotProduct_mulVec,vecMul_transpose,dotProduct_comm,←mulVec_mulVec,dotProduct_mulVec]

lemma recover (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹) :
    P*R*Rᵀ=1 ∧ (P*R)*(P*R)ᵀ=P := by
  have hPP : P*P⁻¹=1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP.isUnit)
  constructor
  · rw [Matrix.mul_assoc,hRR,hPP]
  · rw [transpose_mul,symmetric_of_psd hP.posSemidef,←Matrix.mul_assoc,Matrix.mul_assoc P R Rᵀ,hRR,hPP,Matrix.one_mul]

lemma congruence_outer (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    vecMulVec (Rᵀ*ᵥb) (Rᵀ*ᵥb) = Rᵀ*vecMulVec b b*R := by
  rw [mul_vecMulVec,vecMulVec_mul,←vecMul_transpose Rᵀ,transpose_transpose]

lemma congruence_sum_outer (R : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin m → Fin n → ℝ) (A : Finset (Fin m)) :
    (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) = Rᵀ*(∑e∈A,vecMulVec (b e) (b e))*R := by
  simp only [congruence_outer,Matrix.mul_sum,Matrix.sum_mul]

lemma cov_bound (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹)
    (b : Fin m → Fin n → ℝ) (hb : (∑e,vecMulVec (b e) (b e)) ≤ P) :
    (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ≤ (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [congruence_sum_outer]
  exact (congruence_mono hb R).trans (normalized_covariance P hP R hRR)

lemma transfer (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹)
    (b : Fin m → Fin n → ℝ) (A : Finset (Fin m)) {ε : ℝ}
    (h : -(ε • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e))-(1/2:ℝ) • (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ∧
      (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e))-(1/2:ℝ) • (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ≤ ε • 1) :
    -(ε • P) ≤ (∑e∈A,vecMulVec (b e) (b e))-(1/2:ℝ) • (∑e,vecMulVec (b e) (b e)) ∧
      (∑e∈A,vecMulVec (b e) (b e))-(1/2:ℝ) • (∑e,vecMulVec (b e) (b e)) ≤ ε • P := by
  let S := P*R
  have hu := congruence_mono h.2 Sᵀ
  have hl := congruence_mono h.1 Sᵀ
  have hs : S*Rᵀ=1 := (recover P hP R hRR).1
  have hss : S*Sᵀ=P := (recover P hP R hRR).2
  have ht : R*Sᵀ=1 := by
    have hh := congrArg transpose hs
    simpa only [transpose_mul,transpose_transpose,transpose_one] using hh
  have simplify (F : Matrix (Fin n) (Fin n) ℝ) : S*(Rᵀ*F*R)*Sᵀ=F := by
    rw [Matrix.mul_assoc Rᵀ F R,←Matrix.mul_assoc S Rᵀ,hs,Matrix.one_mul,Matrix.mul_assoc,ht,Matrix.mul_one]
  simp only [transpose_transpose,congruence_sum_outer,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,simplify,hss,Matrix.mul_neg,Matrix.neg_mul] at hu hl
  exact ⟨hl,hu⟩

def rationalFactor (P : Matrix (Fin n) (Fin n) ℚ) :=
  RationalGram.factorMatrix (RationalInverse.inverse n P)

lemma cast_inverse (P : Matrix (Fin n) (Fin n) ℚ) :
    (P⁻¹).map (fun q : ℚ => (q:ℝ)) = (P.map (fun q : ℚ => (q:ℝ)))⁻¹ := by
  have hadj : P.adjugate.map (fun q : ℚ => (q:ℝ)) =
      (P.map (fun q : ℚ => (q:ℝ))).adjugate := (Rat.castHom ℝ).map_adjugate P
  rw [Matrix.inv_def,Matrix.inv_def,Ring.inverse_eq_inv,Ring.inverse_eq_inv]
  ext i j
  simp only [map_apply,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul,Rat.cast_inv]
  rw [←Rat.cast_det]
  have hh := congrFun (congrFun hadj i) j
  exact congrArg ((P.det:ℝ)⁻¹ * ·) hh

lemma rationalFactor_correct (P : Matrix (Fin n) (Fin n) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) :
    (rationalFactor P).map (fun q : ℚ => (q:ℝ)) *
      ((rationalFactor P).map (fun q : ℚ => (q:ℝ)))ᵀ = (P.map (fun q : ℚ => (q:ℝ)))⁻¹ := by
  unfold rationalFactor
  rw [RationalInverse.inverse_eq_of_cast P hP]
  have hInv : (P⁻¹.map (fun q : ℚ => (q:ℝ))).PosSemidef := by
    rw [cast_inverse]; exact hP.inv.posSemidef
  have hh := congrArg (fun M => M.map (fun q : ℚ => (q:ℝ)))
    (RationalGram.factorMatrix_correct P⁻¹ hInv)
  change (RationalGram.factorMatrix P⁻¹ * (RationalGram.factorMatrix P⁻¹)ᵀ).map
    (Rat.castHom ℝ) = _ at hh
  rw [Matrix.map_mul] at hh
  exact hh.trans (cast_inverse P)

end AlgorithmicThinTrees.GramWhitening
end

end OAI
