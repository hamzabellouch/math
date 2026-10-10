import OAI.Analysis.GroupDeterminants.RationalRepresentation

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section ProjectionCriterion
variable {G r m : Type} [Group G] [Group.FG G]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m] [Nonempty r]

theorem projection_criterion (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P ∧ IsSelfAdjoint P)
    (htrace : (Fintype.card r : ℚ) < ∑ i, (P i i).coeff 1)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2)) :
    MainStatement := by
  obtain ⟨k, hk, hq, hqD⟩ := exists_binary_modulus D hodd.pos hodd
  obtain ⟨U, V, A, hA, hAu⟩ := integral_transfer_of_congruence D hodd P hP.1 Z hZ u v huv k hk hqD
  let e := Fintype.equivFin (r ⊕ m)
  let A' := Matrix.reindex e e A
  have hAu' : IsUnit (rationalMatrix A') := reindexed_rational_isUnit A hAu
  have hqR : (1 : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast hq
  have hPC : P.map rationalComplexMap * P.map rationalComplexMap = P.map rationalComplexMap := by
    rw [← Matrix.map_mul, hP.1]
  have hOp : regularOperator A' = indexedComplexRepresentation
      (transferMatrix (((2 ^ k : ℕ) : ℚ) : ℝ) (P.map rationalComplexMap)
        ((U.map toRat).map rationalComplexMap) ((V.map toRat).map rationalComplexMap)) := by
    rw [← rationalIndexed_integer A, hA, transferMatrix_map_complex]
  have hlog := transfer_trace_log (((2 ^ k : ℕ) : ℚ) : ℝ)
    (lt_trans zero_lt_one hqR) (P.map rationalComplexMap) hPC
      ((U.map toRat).map rationalComplexMap) ((V.map toRat).map rationalComplexMap)
  dsimp only at hlog
  rw [← hOp, rationalComplexMap_trace] at hlog
  have htraceR : (Fintype.card r : ℝ) < ((∑ i, (P i i).coeff 1 : ℚ) : ℝ) := by
    exact_mod_cast htrace
  have hn : 2 * ((Fintype.card r : ℝ) - ((∑ i, (P i i).coeff 1 : ℚ) : ℝ)) *
      Real.log (((2 ^ k : ℕ) : ℚ) : ℝ) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr htraceR))
      (Real.log_pos (by simpa using hqR))
  refine ⟨G, inferInstance, inferInstance, Fintype.card (r ⊕ m),
    Fintype.card_pos, A', regularOperator A', hAu', regularOperator_spec A',
    regularOperator_isUnit hAu', fkDet_pos _, ?_⟩
  unfold fkDet
  apply Real.exp_lt_one_iff.mpr
  rw [hlog, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos hn (by norm_num)

end ProjectionCriterion
end GroupRingDeterminant

end

end OAI
