import OAI.NumberTheory.EgyptianFractions.DiscreteSecondDerivative
import OAI.NumberTheory.EgyptianFractions.SecondDifference
import OAI.NumberTheory.EgyptianFractions.PhaseExtension

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

/-- The discrete test needs monotonicity only at the sampled increments. -/
theorem discrete_second_derivative_sqrt_bound_local (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧
      f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  obtain ⟨g, hgf, hgm, hgd⟩ := exists_monotone_increment_extension f N
    (Nat.pos_of_ne_zero hN) hmono
  have h := discrete_second_derivative_sqrt_bound g N lam A L hlam hlam1 hA (hgm.monotoneOn _)
    (by
      intro i hi j hj hij
      rw [hgd i hi, hgd j hj]
      exact hsep i hi j hj hij)
    (by
      intro j hj
      rw [hgd j hj]
      exact hrange j hj)
  have heq : (∑ j ∈ Finset.range N, phase (g j)) =
      ∑ j ∈ Finset.range N, phase (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hgf j (Finset.mem_range.mp hj).le]
  rwa [heq] at h

/-- Sampled differences on a translated real interval. The closed support ends
at the last needed phase value, not one integer beyond it. -/
theorem translated_sampled_increment_bounds (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N i j : ℕ) (L U : ℝ) (_hi : i < N) (hj : j < N) (hij : i ≤ j)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((j : ℝ) - i) ≤
        (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ∧
      (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ≤ U * ((j : ℝ) - i) := by
  have hsupport (y : ℝ) (hy : y ∈ Set.Icc (i : ℝ) ((j : ℝ) + 1)) :
      y + x ∈ Set.Icc x (x + N) := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    constructor <;> linarith [hy.1, hy.2]
  have h := sampled_increment_bounds
    (fun y => f (y + x)) (fun y => f' (y + x)) (fun y => f'' (y + x))
    i j L U hij
    (fun y hy => (hf (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => (hf' (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => hbound (y + x) (hsupport y hy))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The second-derivative test for a positive second derivative on precisely
the closed interval supporting the finite sum. -/
theorem second_derivative_sqrt_bound_positive (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ f'' y ∧ f'' y ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let g : ℕ → ℝ := fun j => f ((j : ℝ) + x)
  have hb (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) (hij : i ≤ j) :=
    translated_sampled_increment_bounds f f' f'' x N i j lam (A * lam)
      hi hj hij hf hf' hbound
  apply discrete_second_derivative_sqrt_bound_local g N lam A (g 1 - g 0)
    hlam hlam1 hA
  · intro i hi j hj hij
    have hh := (hb i hi j hj hij).1
    have hd : (0 : ℝ) ≤ (j : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hij)
    have hp : 0 ≤ lam * ((j : ℝ) - i) := mul_nonneg hlam.le hd
    dsimp [g]
    linarith
  · intro i hi j hj hij
    exact (hb i hi j hj hij).1
  · intro j hj
    have hh := hb 0 hNpos j hj (Nat.zero_le j)
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj.le
    have hp : 0 ≤ A * lam := mul_nonneg hA hlam.le
    have ht := mul_le_mul_of_nonneg_left hjN hp
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hl := mul_nonneg hlam.le hj0
    dsimp [g]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add] at hh ⊢
    constructor <;> linarith [hh.1, hh.2]

/-- The usual absolute second-derivative test. Darboux gives a uniform sign;
negative phases are handled by complex conjugation. -/
theorem second_derivative_sqrt_bound (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  rcases second_derivative_signed_bounds f' f'' _ (convex_Icc _ _) lam (A * lam)
      hlam hf' hbound with hpos | hneg
  · exact second_derivative_sqrt_bound_positive f f' f'' x N lam A
      hlam hlam1 hA hf hf' hpos
  · have h := second_derivative_sqrt_bound_positive
      (fun y => -f y) (fun y => -f' y) (fun y => -f'' y) x N lam A
      hlam hlam1 hA
      (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
      (by
        intro y hy
        have hh := hneg y hy
        constructor <;> linarith [hh.1, hh.2])
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using h

/-- Natural interval form, requiring derivative bounds only on its closure. -/
theorem second_derivative_sqrt_bound_Ico (f f' f'' : ℝ → ℝ)
    (a b : ℕ) (lam A : ℝ) (hab : a ≤ b)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.Ico a b, phase (f j)‖ ≤
      6 * A * (b - a : ℕ) * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have hend : (a : ℝ) + (b - a : ℕ) = (b : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hab)
  have h := second_derivative_sqrt_bound f f' f'' (a : ℝ) (b - a) lam A
    hlam hlam1 hA (by simpa only [hend] using hf)
    (by simpa only [hend] using hf') (by simpa only [hend] using hbound)
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add, add_comm] using h

/-- A uniform second-derivative estimate for every positive scale, without a
smallness hypothesis on that scale or an additive endpoint error. -/
theorem second_derivative_test (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      (6 * A + 15) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hNs : 0 ≤ (N : ℝ) * Real.sqrt lam := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hinv : 0 ≤ 1 / Real.sqrt lam := by positivity
  by_cases hl1 : lam ≤ 1
  · have h := second_derivative_sqrt_bound f f' f'' x N lam A hlam hl1 hA hf hf' hbound
    have hs1 : Real.sqrt lam ≤ 1 := by nlinarith [Real.sq_sqrt hlam.le]
    have hi1 : 1 ≤ 1 / Real.sqrt lam := (le_div_iff₀ hs).2 (by simpa using hs1)
    have ha := mul_nonneg hA hinv
    apply h.trans
    have heq : 6 * A * N * Real.sqrt lam = 6 * A * ((N : ℝ) * Real.sqrt lam) := by ring
    rw [heq]
    simp only [div_eq_mul_inv, one_mul] at hi1 ha ⊢
    nlinarith
  · have hs1 : 1 ≤ Real.sqrt lam := by nlinarith [Real.sq_sqrt hlam.le]
    have hnorm : ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, ‖phase (f ((j : ℝ) + x))‖ := norm_sum_le _ _
        _ = (N : ℝ) := by simp only [phase_norm, Finset.sum_const, Finset.card_range,
                            nsmul_eq_mul, mul_one]
    apply hnorm.trans
    have hN := mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have ha := mul_nonneg hA (add_nonneg hNs hinv)
    nlinarith

/-- Interval version of the uniform second-derivative test. -/
theorem second_derivative_test_Ico (f f' f'' : ℝ → ℝ)
    (a b : ℕ) (lam A : ℝ) (hab : a ≤ b) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.Ico a b, phase (f j)‖ ≤
      (6 * A + 15) * (((b - a : ℕ) : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  have hend : (a : ℝ) + (b - a : ℕ) = (b : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hab)
  have h := second_derivative_test f f' f'' (a : ℝ) (b - a) lam A
    hlam hA (by simpa only [hend] using hf)
    (by simpa only [hend] using hf') (by simpa only [hend] using hbound)
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add, add_comm] using h

end Problem337.ExponentialSum

end OAI
