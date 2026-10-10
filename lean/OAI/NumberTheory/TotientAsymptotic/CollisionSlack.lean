import OAI.NumberTheory.TotientAsymptotic.CollisionAlgebra
import OAI.NumberTheory.TotientAsymptotic.PublishedComparison

namespace OAI

/-! Quantitative strict slack in the published comparison exponent. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_a_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, a j) = (n+1 : ℝ)*Real.log (n+1)-n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [a, Nat.cast_add, Nat.cast_one]
    ring

/-- Moving each surviving cutoff by at most `e` loses only `e * sum a_k`
of the strict simplex slack. The weights are compared at the original indices. -/
lemma gridded_weighted_slack (b J : ℕ) (j : ℕ → ℕ) (u ν : ℕ → ℝ)
    (B σ e : ℝ) (hB : 0 < B)
    (hj : Set.InjOn j (↑(Finset.Icc 1 b) : Set ℕ))
    (hidx : ∀ k ∈ Finset.Icc 1 b, k ≤ j k ∧ j k ≤ J)
    (hu : ∀ k ∈ Finset.Icc 1 J, 0 ≤ u k)
    (hslack : (∑ k ∈ Finset.Icc 1 J, a k*u k) ≤ (1-σ)*B)
    (hgrid : ∀ k ∈ Finset.Icc 1 b, ν k ≤ u (j k)/B+e) :
    (∑ k ∈ Finset.Icc 1 b, a k*ν k) ≤ 1-σ+e*(∑ k ∈ Finset.Icc 1 b, a k) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 b, a k*(u (j k)/B+e) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hgrid k hk) (a_pos (Finset.mem_Icc.mp hk).1).le
    _ = (∑ k ∈ Finset.Icc 1 b, a k*u (j k))/B+e*(∑ k ∈ Finset.Icc 1 b, a k) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro k hk; ring
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
    _ ≤ (∑ k ∈ Finset.Icc 1 J, a k*u k)/B+e*(∑ k ∈ Finset.Icc 1 b, a k) :=
      add_le_add (div_le_div_of_nonneg_right
        (reindexed_slack_sum_le b J j u hj hidx hu) hB.le) le_rfl
    _ ≤ 1-σ+e*(∑ k ∈ Finset.Icc 1 b, a k) :=
      add_le_add ((div_le_iff₀ hB).mpr hslack) le_rfl

lemma comparisonError_le (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) (w : ℝ)
    (hwidth : ∀ j ∈ Finset.Icc 1 (b-1), B (Y j)/B y-B (U j)/B y ≤ w) :
    comparisonError b y S Y U ≤
      2*(b-1 : ℕ)*w+Real.sqrt (B S/B y)*
        ∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i) := by
  unfold comparisonError
  have hh := Finset.sum_le_sum hwidth
  have hc : (∑ _j ∈ Finset.Icc 1 (b-1), w) = (b-1 : ℕ)*w := by simp
  rw [hc] at hh
  linarith

lemma comparisonExponent_le (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ)
    (σ e w : ℝ)
    (hweighted : (∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y)) ≤
      1-σ+e*(∑ j ∈ Finset.Icc 1 (b-1), a j))
    (hwidth : ∀ j ∈ Finset.Icc 1 (b-1), B (Y j)/B y-B (U j)/B y ≤ w)
    (herror : e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
      Real.sqrt (B S/B y)*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤ σ/2) :
    -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
      comparisonError b y S Y U ≤ -1-σ/2 := by
  have hh := comparisonError_le b y S Y U w hwidth
  linarith

lemma comparison_log_power_saving {y E σ : ℝ} (hy : 1 ≤ Real.log y)
    (hE : E ≤ -1-σ) :
    (Real.log y)^E ≤ (Real.log y)⁻¹*Real.exp (-σ*B y) := by
  calc
    _ ≤ (Real.log y)^(-1-σ) := Real.rpow_le_rpow_of_exponent_le hy hE
    _ = (Real.log y)⁻¹*Real.exp (-σ*B y) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hy)]
      change Real.exp (B y*(-1-σ)) = _
      rw [mul_sub, mul_neg_one, Real.exp_sub, Real.exp_neg]
      rw [show Real.exp (B y) = Real.log y from
        Real.exp_log (lt_of_lt_of_le zero_lt_one hy)]
      rw [neg_mul, Real.exp_neg]
      simp [div_eq_mul_inv, mul_comm]

end TotientAsymptotic

end

end OAI
