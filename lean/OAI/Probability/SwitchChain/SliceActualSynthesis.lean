import OAI.Probability.SwitchChain.SliceNormalizedFamily
import OAI.Probability.SwitchChain.SliceSynthesis
import OAI.Probability.SwitchChain.SliceGeneratorEquality
import OAI.Probability.SwitchChain.SliceImageNorm

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_equalityVector (q : ℕ) (i j : V) :
    raw q i j = SliceEuclideanGenerator.equalityVector q
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  ext S
  rw [SliceEuclideanGenerator.equalityVector_apply]
  rfl

 theorem synthesis_column (q : ℕ) (c : V → V → ℝ) :
    synthesis (column q) (ofMatrix c) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, c i j • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  simp only [synthesis_ofMatrix, column, raw_eq_equalityVector,
    Finset.smul_sum, smul_smul]
  simp only [mul_comm]

 theorem synthesis_linearPair_column (q : ℕ) (u : V → ℝ) :
    synthesis (column q) (ofMatrix (linearPair u)) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, (u i + u j) • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  rw [synthesis_column]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [← raw_eq_equalityVector, raw_diag]
    simp
  · simp [linearPair, hij]

 theorem generator_synthesis_linear (q : ℕ) (u : V → ℝ) (hu : ∑ i, u i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix (linearPair u))) =
      ((Fintype.card V : ℝ) / 2) • synthesis (column q) (ofMatrix (linearPair u)) := by
  rw [synthesis_linearPair_column, map_smul,
    SliceEuclideanGenerator.generator_additive_equality q _ u hu, smul_smul,
    smul_smul]
  congr 1
  ring

 theorem generator_synthesis_rowZero (q : ℕ) (c : V → V → ℝ)
    (hrow : ∀ i, rowSum c i = 0) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix c)) =
      ((Fintype.card V : ℝ) - 1) • synthesis (column q) (ofMatrix c) := by
  have hcol : ∀ j, ∑ i, c i j = 0 := by
    intro j
    simpa only [rowSum, hsym] using hrow j
  rw [synthesis_column, map_smul,
    SliceEuclideanGenerator.generator_rowzero_equality q _ c hdiag hrow hcol,
    smul_smul, smul_smul]
  congr 1
  ring

 theorem synthesis_column_eq_vector (q : ℕ) (c : V → V → ℝ)
    (hdiag : ∀ i, c i i = 0) :
    synthesis (column q) (ofMatrix c) = (2 / denominator V q) •
      SliceMoments.vector Finset.univ q (SliceImageNorm.equalityImage q c) := by
  ext S
  simp only [synthesis_ofMatrix, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, column, raw, 
    SliceMoments.vector, SliceImageNorm.equalityImage]
  have hterm (i j : V) : c i j * ((denominator V q)⁻¹ *
      (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val)) =
      (denominator V q)⁻¹ *
        (c i j * SliceMoments.centeredEqual Finset.univ q i j S.val) := by
    by_cases hij : i = j
    · subst j; simp [hdiag]
    · simp only [hij, ite_false]; ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

 theorem synthesis_linear_norm_sq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V)
    (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ‖synthesis (column q) (ofMatrix (linearPair u))‖ ^ 2 =
      SliceImageNorm.linearGramScalar (α := V) q * ‖ofMatrix (linearPair u)‖ ^ 2 := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  have hd := denominator_sq (V := V) q hp.le hp1.le
  have hdenpos : 0 < denominator V q := by
    apply Real.sqrt_pos.2
    have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
      exact_mod_cast Nat.choose_pos hqN.le
    exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)
  have hcoeff : ‖ofMatrix (linearPair u)‖ ^ 2 =
      ∑ i, ∑ j, (linearPair u i j)^2 := by
    rw [← real_inner_self_eq_norm_sq, ofMatrix_inner]
    simp only [pow_two]
  rw [synthesis_column_eq_vector q _ (linearPair_diag u), norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, SliceMoments.vector_norm_sq _ q
      (by simpa using hqN.le), Finset.card_univ,
    SliceImageNorm.average_equalityImage_linearPair_sq_ratio hN q hqN.le hp.ne' u hu,
    hcoeff, div_pow, hd]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hqN.le).ne'
  have hp0 := hp.ne'
  have hp10 : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI
