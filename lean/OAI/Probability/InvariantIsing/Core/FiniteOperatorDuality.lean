import OAI.Probability.InvariantIsing.Core.CubeOperatorNorm

namespace OAI

/-! Euclidean / finite sup-norm duality for the rectangular operator. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace InvariantIsing

lemma finite_operator_duality {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : (Fin N → ℝ) →L[ℝ] E) (S : E →L[ℝ] PiLp 1 (fun _ : Fin N => ℝ))
    (hpair : ∀ x y, ⟪T x, y⟫_ℝ = ∑ i, x i*(S y) i) : ‖S‖=‖T‖ := by
  apply le_antisymm
  · apply S.opNorm_le_bound (norm_nonneg T)
    intro y
    let σ : Spin N := fun i => decide (0 ≤ (S y) i)
    have hsum : ‖S y‖ = ⟪T (fun i => spinValue (σ i)), y⟫_ℝ := by
      rw [PiLp.norm_eq_of_L1,hpair]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [σ]
      by_cases hi : 0 ≤ (S y) i
      · simp [spinValue,hi,abs_of_nonneg hi]
      · simp [spinValue,hi,abs_of_neg (lt_of_not_ge hi)]
    have hs : ‖(fun i => spinValue (σ i))‖ ≤ (1 : ℝ) :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp [Real.norm_eq_abs]
    rw [hsum]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((T.le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg T) hs)) (norm_nonneg y))
  · apply T.opNorm_le_bound (norm_nonneg S)
    intro x
    by_cases hx : ‖T x‖=0
    · rw [hx]
      positivity
    have hsum : ⟪T x, T x⟫_ℝ ≤ ‖x‖*‖S (T x)‖ := by
      rw [hpair,PiLp.norm_eq_of_L1,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hi : |x i|≤‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
      exact (le_abs_self (x i*(S (T x)) i)).trans (by
        rw [abs_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hi (abs_nonneg _))
    rw [real_inner_self_eq_norm_sq] at hsum
    have hbound := (S.le_opNorm (T x))
    have hmul := mul_le_mul_of_nonneg_left hbound (norm_nonneg x)
    have hpos : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      ‖T x‖*‖T x‖ = ‖T x‖^2 := by ring
      _ ≤ ‖x‖*‖S (T x)‖ := hsum
      _ ≤ ‖x‖*(‖S‖*‖T x‖) := hmul
      _ = (‖S‖*‖x‖)*‖T x‖ := by ring

end InvariantIsing

end

end OAI
