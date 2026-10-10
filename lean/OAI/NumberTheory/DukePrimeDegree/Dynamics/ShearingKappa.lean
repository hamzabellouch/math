import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingDiagonal
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# A scale for noncentral return matrices

The scale is the maximum of the diagonal difference and a homogeneous
off-diagonal size. The latter uses the square root of the quadratic
coefficient and a finite sum of the other linear coefficients. This
equivalent choice of norm gives exactly the two scaling regimes used in
EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootShearingOffDiagonalSize {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  ∑ k, if k = i ∨ k = j then 0 else |g.val j k| + |g.val k i|

def rootShearingMovingSize {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  Real.sqrt |g.val j i| + rootShearingOffDiagonalSize i j g

def rootShearingKappa {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  max |g.val j j - g.val i i| (rootShearingMovingSize i j g)

lemma rootShearingOffDiagonalSize_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingOffDiagonalSize i j g := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

lemma rootShearingOffDiagonalSize_row_bound {n : ℕ} {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (g : G n) :
    |g.val j k| ≤ rootShearingOffDiagonalSize i j g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun k => if k = i ∨ k = j then (0 : ℝ) else |g.val j k| + |g.val k i|)
    (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
  simp only [hki, hkj, false_or, ite_false] at h
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans h

lemma rootShearingOffDiagonalSize_col_bound {n : ℕ} {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (g : G n) :
    |g.val k i| ≤ rootShearingOffDiagonalSize i j g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun k => if k = i ∨ k = j then (0 : ℝ) else |g.val j k| + |g.val k i|)
    (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
  simp only [hki, hkj, false_or, ite_false] at h
  exact (le_add_of_nonneg_left (abs_nonneg _)).trans h

lemma rootShearingMovingSize_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingMovingSize i j g :=
  add_nonneg (Real.sqrt_nonneg _) (rootShearingOffDiagonalSize_nonneg i j g)

lemma rootShearingKappa_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingKappa i j g :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem rootShearingKappa_pos_of_noncentral {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) :
    0 < rootShearingKappa i j g := by
  by_contra hn
  have hk : rootShearingKappa i j g ≤ 0 := le_of_not_gt hn
  have ha : |g.val j j - g.val i i| ≤ 0 := (le_max_left _ _).trans hk
  have hb : rootShearingMovingSize i j g ≤ 0 := (le_max_right _ _).trans hk
  have hoff := rootShearingOffDiagonalSize_nonneg i j g
  have hsqrt := Real.sqrt_nonneg |g.val j i|
  have hsqrtzero : Real.sqrt |g.val j i| = 0 := by
    dsimp [rootShearingMovingSize] at hb
    linarith
  have hji : g.val j i = 0 := abs_eq_zero.mp ((Real.sqrt_eq_zero (abs_nonneg _)).mp hsqrtzero)
  have hoffzero : rootShearingOffDiagonalSize i j g = 0 := by
    dsimp [rootShearingMovingSize] at hb
    linarith
  have hdiag : g.val i i = g.val j j := by
    have hz := abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    linarith
  apply hnot
  apply (commutes_root_one_iff_all hij g).mp
  apply (commutes_root_one_iff hij g).mpr
  refine ⟨?_, ?_, hdiag⟩
  · intro k hki
    by_cases hkj : k = j
    · simpa only [hkj] using hji
    · exact abs_eq_zero.mp (le_antisymm
        (hoffzero ▸ rootShearingOffDiagonalSize_col_bound hki hkj g) (abs_nonneg _))
  · intro k hkj
    by_cases hki : k = i
    · simpa only [hki] using hji
    · exact abs_eq_zero.mp (le_antisymm
        (hoffzero ▸ rootShearingOffDiagonalSize_row_bound hki hkj g) (abs_nonneg _))

theorem rootShearingMovingSize_conjugate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    rootShearingMovingSize i j (rootPairConjugate i j t g) =
      Real.exp t * rootShearingMovingSize i j g := by
  have hquad : Real.sqrt |(rootPairConjugate i j t g).val j i| =
      Real.exp t * Real.sqrt |g.val j i| := by
    rw [rootPairConjugate_quadratic hij, abs_mul, abs_of_pos (Real.exp_pos _),
      Real.sqrt_mul (Real.exp_pos _).le]
    have he : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
      rw [show 2 * t = t + t by ring, Real.exp_add, pow_two]
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hoff : rootShearingOffDiagonalSize i j (rootPairConjugate i j t g) =
      Real.exp t * rootShearingOffDiagonalSize i j g := by
    unfold rootShearingOffDiagonalSize
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = i ∨ k = j
    · simp only [hk, ite_true, mul_zero]
    · have hki : k ≠ i := fun h => hk (Or.inl h)
      have hkj : k ≠ j := fun h => hk (Or.inr h)
      simp only [hk, ite_false, rootPairConjugate_row hij hki hkj,
        rootPairConjugate_col hij hki hkj, abs_mul, abs_of_pos (Real.exp_pos t), mul_add]
  simp only [rootShearingMovingSize, hquad, hoff, mul_add]

theorem rootShearingKappa_conjugate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    rootShearingKappa i j (rootPairConjugate i j t g) =
      max |g.val j j - g.val i i| (Real.exp t * rootShearingMovingSize i j g) := by
  simp only [rootShearingKappa, rootPairConjugate_diagonal,
    rootShearingMovingSize_conjugate hij]

theorem continuous_rootShearingKappa {n : ℕ} (i j : Fin n) :
    Continuous (rootShearingKappa i j) := by
  have hc (r s : Fin n) : Continuous (fun g : G n => g.val r s) := by fun_prop
  unfold rootShearingKappa rootShearingMovingSize rootShearingOffDiagonalSize
  apply Continuous.max ((hc j j).sub (hc i i)).abs
  apply Continuous.add ((hc j i).abs.sqrt)
  apply continuous_finsetSum
  intro k _
  split_ifs
  · exact continuous_const
  · exact (hc j k).abs.add (hc k i).abs

end DukePrimeDegree

end

end OAI
