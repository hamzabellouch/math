import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamilyBounds

namespace OAI

/-! Internal physical exchange fields retain bounds in every tensor block. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourExchange_pauli (p q : Fin 4) (hpq : p ≠ q) :
    qmaFourExchange p q = ∑ μ : Fin 3, qmaFourSpin p μ*qmaFourSpin q μ := by
  rw [qmaFourExchange_source]
  change (sourceHeisenbergMatrix 4 p q).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm = _
  rw [← sourceLocalPauli_sum 4 p q hpq,MediatorGraph.submatrix_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,qmaFourSpin_source,qmaFourSpin_source]
  rfl

theorem qmaFourSpin_commute (p q : Fin 4) (hpq : p ≠ q) (μ ν : Fin 3) :
    qmaFourSpin p μ*qmaFourSpin q ν = qmaFourSpin q ν*qmaFourSpin p μ := by
  simp only [qmaFourSpin_source]
  change (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 q ν).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm =
    (sourceLocalPauli 4 q ν).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm
  rw [Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,sourceLocalPauli_commute 4 p q hpq]

theorem qmaFourExchange_star (p q : Fin 4) (hpq : p ≠ q) :
    (qmaFourExchange p q).conjTranspose = qmaFourExchange p q := by
  simp only [qmaFourExchange_pauli p q hpq,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    qmaFourSpin_star,qmaFourSpin_commute q p (Ne.symm hpq)]

theorem qmaFourTensorExchange_norm (i : Fin n) (p q : Fin 4) (hpq : p ≠ q) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange p q))‖ ≤ 3 := by
  rw [qmaFourExchange_pauli p q hpq,qmaSiteMatrix_sum,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourSpin p μ*qmaFourSpin q μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      rw [← qmaSiteMatrix_mul,spinMatrixOperator_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using (mul_le_mul (qmaFourTensorSpin_norm i p μ) (qmaFourTensorSpin_norm i q μ)
          (norm_nonneg _) zero_le_one))
    _ = 3 := by norm_num

theorem qmaSiteMatrix_neg (i : Fin n) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (-A) = -qmaSiteMatrix i A := by
  rw [← neg_one_smul ℂ A,qmaSiteMatrix_smul,neg_one_smul]

theorem qmaSiteMatrix_sub (i : Fin n) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (A-B) = qmaSiteMatrix i A-qmaSiteMatrix i B := by
  simp only [sub_eq_add_neg,qmaSiteMatrix_add,qmaSiteMatrix_neg]

theorem qmaFourField_star (x z : ℝ) : (qmaFourField x z).conjTranspose = qmaFourField x z := by
  simp only [qmaFourField,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Complex.star_def,Complex.conj_ofReal,qmaFourExchange_star 0 3 (by decide),
    qmaFourExchange_star 0 2 (by decide),qmaFourExchange_star 0 1 (by decide)]

theorem qmaFourTensorField_norm (i : Fin n) (x z : ℝ) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourField x z))‖ ≤ 6*(|x|+|z|) := by
  have hs : 1 ≤ Real.sqrt 3 := by
    have h0 := Real.sqrt_nonneg 3
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    nlinarith
  have hx : |x/(2*Real.sqrt 3)| ≤ |x| := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt 3)]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt 3)).mpr
    nlinarith [abs_nonneg x]
  have hz : |z/2| ≤ |z| := by rw [abs_div]; norm_num
  rw [qmaFourField,qmaSiteMatrix_sub,qmaSiteMatrix_smul,qmaSiteMatrix_smul,
    qmaSiteMatrix_sub,spinMatrixOperator_sub,spinMatrixOperator_smul,spinMatrixOperator_smul]
  have hdiff : ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 3)-
      qmaSiteMatrix i (qmaFourExchange 0 2))‖ ≤ 6 := by
    rw [spinMatrixOperator_sub]
    exact (norm_sub_le _ _).trans ((add_le_add (qmaFourTensorExchange_norm i 0 3 (by decide))
      (qmaFourTensorExchange_norm i 0 2 (by decide))).trans_eq (by norm_num))
  have hlast := qmaFourTensorExchange_norm i 0 1 (by decide)
  calc
    _ ≤ ‖((x/(2*Real.sqrt 3):ℝ):ℂ) • spinMatrixOperator
          (qmaSiteMatrix i (qmaFourExchange 0 3)-qmaSiteMatrix i (qmaFourExchange 0 2))‖+
        ‖((z/2:ℝ):ℂ) • spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 1))‖ := norm_sub_le _ _
    _ = |x/(2*Real.sqrt 3)| * ‖spinMatrixOperator
          (qmaSiteMatrix i (qmaFourExchange 0 3)-qmaSiteMatrix i (qmaFourExchange 0 2))‖+
        |z/2| * ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 1))‖ := by
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |x| * 6+|z| * 3 := add_le_add (mul_le_mul hx hdiff (norm_nonneg _) (abs_nonneg x))
      (mul_le_mul hz hlast (norm_nonneg _) (abs_nonneg z))
    _ ≤ _ := by nlinarith [abs_nonneg z]

theorem qmaFourAxisField_star (a : Fin 2) (t : ℝ) :
    (qmaFourAxisField a t).conjTranspose = qmaFourAxisField a t := by
  unfold qmaFourAxisField
  split_ifs <;> exact qmaFourField_star _ _

theorem qmaFourTensorAxisField_norm (i : Fin n) (a : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourAxisField a t))‖ ≤ 6*|t| := by
  unfold qmaFourAxisField
  split_ifs
  · simpa only [abs_zero,add_zero] using qmaFourTensorField_norm i t 0
  · simpa only [abs_zero,zero_add] using qmaFourTensorField_norm i 0 t

theorem qmaFourTensorCounterterm_star (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorCounterterm i j a b t).conjTranspose = qmaFourTensorCounterterm i j a b t := by
  simp only [qmaFourTensorCounterterm,Matrix.conjTranspose_add,qmaSiteMatrix_star,qmaFourAxisField_star]

theorem qmaFourTensorCounterterm_norm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCounterterm i j a b t)‖ ≤
      6*(|qmaFourCounterA a b t|+|qmaFourCounterB a b t|) := by
  rw [qmaFourTensorCounterterm,spinMatrixOperator_add]
  exact (norm_add_le _ _).trans ((add_le_add (qmaFourTensorAxisField_norm i a _)
    (qmaFourTensorAxisField_norm j b _)).trans_eq (by ring))

end ContinuumCoulomb

end

end OAI
