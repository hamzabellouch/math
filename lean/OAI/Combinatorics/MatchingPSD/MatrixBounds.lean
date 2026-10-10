import OAI.Combinatorics.MatchingPSD.BitTests

namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma entry_product_bound {a x y b : ℝ} (hb : 0 ≤ b) (ha : |a| ≤ b) :
    x*a*y ≤ b*(x^2+y^2)/2 := by
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have he : x*a*y ≤ b*(|x| * |y|) := by
    calc
      _ ≤ |x*a*y| := le_abs_self _
      _ = |a| *(|x| * |y|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hxy hb]

lemma le_card_entry_bound {E : Matrix R R ℝ} (hE : E.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i j, |E i j| ≤ b) :
    E ≤ ((Fintype.card R : ℝ)*b) • (1 : Matrix R R ℝ) := by
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (.of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb))).sub hE
  · intro x
    have hsum : (∑ i, ∑ j, x i*E i j*x j) ≤
        (Fintype.card R : ℝ)*b*(∑ i, (x i)^2) := by
      calc
        _ ≤ ∑ i, ∑ j, (b/2*(x i)^2 + b/2*(x j)^2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have he := entry_product_bound (x := x i) (y := x j) hb (hbound i j)
          linarith
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, star_trivial]
    rw [sub_nonneg]
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, pow_two, smul_eq_mul, mul_assoc] using hsum

lemma posSemidef_entry_abs_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) (i j : R) :
    |A i j| ≤ A.trace := by
  have hi : 0 ≤ A i i := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1)
    simpa using he
  have hj : 0 ≤ A j j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single j 1)
    simpa using he
  have hsym : A j i = A i j := by
    simpa using congrArg (fun M : Matrix R R ℝ => M i j) hA.isHermitian.eq
  have hplus : -(A i i + A j j)/2 ≤ A i j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hminus : A i j ≤ (A i i + A j j)/2 := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
      sub_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hdiag (k : R) : A k k ≤ A.trace := by
    change A k k ≤ ∑ l, A l l
    apply Finset.single_le_sum (f := fun l => A l l)
    · intro l _
      have he := hA.dotProduct_mulVec_nonneg (Pi.single l 1)
      simpa using he
    · exact Finset.mem_univ k
  exact (abs_le.mpr ⟨by linarith, hminus⟩).trans (by linarith [hdiag i, hdiag j])

omit [Fintype R] [DecidableEq R] in
lemma matrix_sum_psd {X : Type u_2} (s : Finset X) (f : X → Matrix R R ℝ)
    (hf : ∀ x ∈ s, (f x).PosSemidef) : (∑ x ∈ s, f x).PosSemidef :=
  (Finset.sum_nonneg (fun x hx => (hf x hx).nonneg)).posSemidef

end PerfectMatchingPSD

end OAI
