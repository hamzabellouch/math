import OAI.Combinatorics.ContingencyTables.Transport.ProductIntegerSignature
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# The actual positive scalar softening factors

Absolute affine deviations, positive parts and interval distances have
convex integer exponents. Their powers of two are positive log-concave
sequences, supplying the concrete line and unary factors of both papers.
-/

namespace ContingencyTables.ScalarPenalty

open scoped BigOperators

noncomputable def factor (A : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ := (2:ℝ)^(-A*p n)

lemma factor_positive (A : ℝ) (p : ℕ → ℝ) (n : ℕ) : 0 < factor A p n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Convex discrete exponents give the exact scalar log-concavity test. -/
theorem factor_logConcave (A : ℝ) (hA : 0 ≤ A) (p : ℕ → ℝ) (n : ℕ)
    (hp : 2*p (n-1) ≤ p n+p (n-2)) :
    factor A p n * factor A p (n-2) ≤ (factor A p (n-1))^2 := by
  unfold factor
  rw [pow_two,← Real.rpow_add (by norm_num : (0:ℝ)<2),
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hp hA]

lemma affine_midpoint (a b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*(a+((n-1:ℕ):ℝ)*b) = (a+(n:ℝ)*b)+(a+((n-2:ℕ):ℝ)*b) := by
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hn]
  norm_num
  ring

lemma abs_affine_convex (a b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*|a+((n-1:ℕ):ℝ)*b| ≤ |a+(n:ℝ)*b|+|a+((n-2:ℕ):ℝ)*b| := by
  have h := abs_add_le (a+(n:ℝ)*b) (a+((n-2:ℕ):ℝ)*b)
  rw [← affine_midpoint a b n hn,abs_mul] at h
  norm_num at h
  exact h

lemma max_convex (p q : ℕ → ℝ) (n : ℕ)
    (hp : 2*p (n-1) ≤ p n+p (n-2)) (hq : 2*q (n-1) ≤ q n+q (n-2)) :
    2*max (p (n-1)) (q (n-1)) ≤ max (p n) (q n)+max (p (n-2)) (q (n-2)) := by
  by_cases h : p (n-1) ≤ q (n-1)
  · rw [max_eq_right h]
    linarith [le_max_right (p n) (q n),le_max_right (p (n-2)) (q (n-2))]
  · rw [max_eq_left (le_of_not_ge h)]
    linarith [le_max_left (p n) (q n),le_max_left (p (n-2)) (q (n-2))]

/-- The row and column absolute-deviation softeners used in both papers. -/
theorem abs_factor_logConcave (A a b : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n) :
    factor A (fun k => |a+(k:ℝ)*b|) n * factor A (fun k => |a+(k:ℝ)*b|) (n-2) ≤
      (factor A (fun k => |a+(k:ℝ)*b|) (n-1))^2 :=
  factor_logConcave A hA _ n (abs_affine_convex a b n hn)

/-- Positive-part small-slot penalties of the first paper. -/
theorem positivePart_factor_logConcave (A a b : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n) :
    factor A (fun k => max (a+(k:ℝ)*b) 0) n * factor A (fun k => max (a+(k:ℝ)*b) 0) (n-2) ≤
      (factor A (fun k => max (a+(k:ℝ)*b) 0) (n-1))^2 := by
  apply factor_logConcave A hA
  exact max_convex (fun k => a+(k:ℝ)*b) (fun _ => 0) n
    (le_of_eq (affine_midpoint a b n hn)) (by simp)

/-- Distance from a physical value ell+n to [0,b]. This formula applies
to the companion's unary tree penalties. -/
noncomputable def intervalDistance (ell b : ℝ) (n : ℕ) : ℝ :=
  max 0 (max (-(ell+(n:ℝ))) (ell+(n:ℝ)-b))

lemma intervalDistance_convex (ell b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*intervalDistance ell b (n-1) ≤ intervalDistance ell b n+intervalDistance ell b (n-2) := by
  unfold intervalDistance
  apply max_convex (fun _ => 0) (fun k => max (-(ell+(k:ℝ))) (ell+(k:ℝ)-b)) n
  · simp
  · apply max_convex (fun k => -(ell+(k:ℝ))) (fun k => ell+(k:ℝ)-b) n
    · have h := affine_midpoint (-ell) (-1) n hn
      convert le_of_eq h using 1 <;> ring
    · have h := affine_midpoint (ell-b) 1 n hn
      convert le_of_eq h using 1 <;> ring

/-- Unary distance softeners are positive and satisfy the exact integer
second-difference inequality needed by the product signature. -/
theorem interval_factor_logConcave (A ell b : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n) :
    factor A (intervalDistance ell b) n * factor A (intervalDistance ell b) (n-2) ≤
      (factor A (intervalDistance ell b) (n-1))^2 :=
  factor_logConcave A hA _ n (intervalDistance_convex ell b n hn)

/-- The positive equality softener tends to its exact equality indicator.
This is the actual finite limiting operation used after marginalization. -/
theorem factor_limit (D : ℝ) (hD : 0 ≤ D) :
    Filter.Tendsto (fun A : ℝ => (2:ℝ)^(-A*D)) Filter.atTop
      (nhds (if D=0 then 1 else 0)) := by
  by_cases hzero : D=0
  · simp [hzero]
  · have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
    let b : ℝ := (2:ℝ)^(-D)
    have hb₀ : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
    have hb₁ : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hpos)
    have hlim := tendsto_rpow_atTop_of_base_lt_one b (by linarith) hb₁
    rw [ite_eq_right hzero]
    convert hlim using 1
    funext A
    dsimp [b]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring

/-- Products of positive scalar log-concave sequences remain log-concave. -/
theorem mul_logConcave (a b : ℕ → ℝ) (n : ℕ)
    (ha : a n*a (n-2) ≤ (a (n-1))^2)
    (hb : b n*b (n-2) ≤ (b (n-1))^2)
    (hapos : 0 ≤ a n*a (n-2)) (hbpos : 0 ≤ b n*b (n-2)) :
    (a n*b n)*(a (n-2)*b (n-2)) ≤ (a (n-1)*b (n-1))^2 := by
  have hh := mul_le_mul ha hb hbpos (hapos.trans ha)
  convert hh using 1 <;> ring

end ContingencyTables.ScalarPenalty

end OAI
