import OAI.MeasureTheory.Falconer.Estimates.TripleGram

namespace OAI

/-! # Stability of the three-direction Gram determinant under projection -/

namespace Falconer
open scoped BigOperators

private theorem product_three_difference {a b c d e f ε : ℝ}
    (_ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hd : |d| ≤ 1) (he : |e| ≤ 1) (_hf : |f| ≤ 1)
    (had : |a-d| ≤ ε) (hbe : |b-e| ≤ ε) (hcf : |c-f| ≤ ε) :
    |a*b*c-d*e*f| ≤ 3*ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans had
  have h₁ : |(a-d)*b*c| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ε*1*1 := by gcongr
      _ = _ := by ring
  have h₂ : |d*(b-e)*c| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ 1*ε*1 := by gcongr
      _ = _ := by ring
  have h₃ : |d*e*(c-f)| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ 1*1*ε := by gcongr
      _ = _ := by ring
  have hi : a*b*c-d*e*f = ((a-d)*b*c+d*(b-e)*c)+d*e*(c-f) := by ring
  rw [hi]
  have hh := (abs_add_le ((a-d)*b*c+d*(b-e)*c) (d*e*(c-f))).trans
    (add_le_add (abs_add_le ((a-d)*b*c) (d*(b-e)*c)) le_rfl)
  linarith

private def determinantTerms (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ :=
  ![A 0 0*A 1 1*A 2 2,-(A 0 0*A 1 2*A 2 1),-(A 0 1*A 1 0*A 2 2),
    A 0 1*A 1 2*A 2 0,A 0 2*A 1 0*A 2 1,-(A 0 2*A 1 1*A 2 0)]

private theorem determinant_eq_sum (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.det = ∑ i, determinantTerms A i := by
  rw [Matrix.det_fin_three]
  simp only [determinantTerms,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  ring

theorem determinant_three_stability (A B : Matrix (Fin 3) (Fin 3) ℝ) {ε : ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) (hB : ∀ i j, |B i j| ≤ 1)
    (hAB : ∀ i j, |A i j-B i j| ≤ ε) : |A.det-B.det| ≤ 18*ε := by
  have hp (i j k l m n : Fin 3) :
      |A i j*A k l*A m n-B i j*B k l*B m n| ≤ 3*ε :=
    product_three_difference (hA i j) (hA k l) (hA m n)
      (hB i j) (hB k l) (hB m n) (hAB i j) (hAB k l) (hAB m n)
  have ht (i : Fin 6) : |determinantTerms A i-determinantTerms B i| ≤ 3*ε := by
    fin_cases i
    · exact hp 0 0 1 1 2 2
    · change |-(A 0 0*A 1 2*A 2 1)-(-(B 0 0*B 1 2*B 2 1))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 0 1 2 2 1
    · change |-(A 0 1*A 1 0*A 2 2)-(-(B 0 1*B 1 0*B 2 2))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 1 1 0 2 2
    · exact hp 0 1 1 2 2 0
    · exact hp 0 2 1 0 2 1
    · change |-(A 0 2*A 1 1*A 2 0)-(-(B 0 2*B 1 1*B 2 0))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 2 1 1 2 0
  rw [determinant_eq_sum,determinant_eq_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 6, |determinantTerms A i-determinantTerms B i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 6, 3*ε := Finset.sum_le_sum (fun i _ => ht i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem gram_three_stability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : Fin 3 → E) {ε : ℝ}
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hclose : ∀ i, ‖u i-v i‖ ≤ ε) :
    |(Matrix.gram ℝ u).det-(Matrix.gram ℝ v).det| ≤ 36*ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hclose 0)
  have hb (a : Fin 3 → E) (ha : ∀ i, ‖a i‖ ≤ 1) (i j : Fin 3) :
      |inner ℝ (a i) (a j)| ≤ 1 := by
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul (ha i) (ha j) (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hd (i j : Fin 3) : |inner ℝ (u i) (u j)-inner ℝ (v i) (v j)| ≤ 2*ε := by
    have he : inner ℝ (u i) (u j)-inner ℝ (v i) (v j) =
        inner ℝ (u i-v i) (u j)+inner ℝ (v i) (u j-v j) := by
      rw [inner_sub_left,inner_sub_right]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    have h₁ : |inner ℝ (u i-v i) (u j)| ≤ ε := by
      apply (abs_real_inner_le_norm _ _).trans
      exact (mul_le_mul (hclose i) (hu j) (norm_nonneg _) hε).trans_eq (mul_one _)
    have h₂ : |inner ℝ (v i) (u j-v j)| ≤ ε := by
      apply (abs_real_inner_le_norm _ _).trans
      exact (mul_le_mul (hv i) (hclose j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    linarith
  have hh := determinant_three_stability (Matrix.gram ℝ u) (Matrix.gram ℝ v)
    (hb u hu) (hb v hv) hd
  linarith

end Falconer

end OAI
