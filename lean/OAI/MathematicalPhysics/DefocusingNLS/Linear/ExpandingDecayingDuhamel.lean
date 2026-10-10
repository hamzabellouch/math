import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightedDuhamel

namespace OAI

/-! # The decaying cutoff residual in the moving-scale Duhamel estimate

The extra `exp(-t)` in the residual is integrable.  Its propagated contribution
therefore retains the free decay with no factor depending on the slab length.
-/

open Set MeasureTheory

namespace DefocusingNLS

private theorem integral_exp_neg_Icc (t : ℝ) (ht : 0 ≤ t) :
    (∫ τ in Icc 0 t, Real.exp (-τ)) = 1 - Real.exp (-t) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have he : (fun τ : ℝ => Real.exp (-τ)) = fun τ => Real.exp ((-1 : ℝ) * τ) := by
    funext τ
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-1 : ℝ) ≠ 0),
    integral_exp]
  simp only [neg_one_mul, mul_zero, Real.exp_zero, inv_neg, inv_one, smul_eq_mul]
  ring

/-- A source with the actual cutoff decay gives a free-decaying response. -/
theorem expandingDuhamel_fast_source_norm_le (a b k L t C : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (r : ℝ → FourierL2)
    (hbound : ∀ τ ∈ Icc 0 t, ‖r τ‖ ≤ C * Real.exp (-(2 + a) * τ / 2)) :
    ‖expandingDuhamel a b k L ha hk hL t r‖ ≤ C * Real.exp (-a * t / 2) := by
  have hg : IntegrableOn (fun τ : ℝ => C * Real.exp (-a * t / 2) * Real.exp (-τ))
      (Icc 0 t) := (by fun_prop : Continuous
        (fun τ : ℝ => C * Real.exp (-a * t / 2) * Real.exp (-τ))).continuousOn.integrableOn_compact
          isCompact_Icc
  have hi : ‖expandingDuhamel a b k L ha hk hL t r‖ ≤
      ∫ τ in Icc 0 t, C * Real.exp (-a * t / 2) * Real.exp (-τ) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
    apply (expandingFreeStep_norm_bound a b k (expandingRadius L τ) (t - τ) ha hk
      (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ)).trans
    calc
      _ ≤ Real.exp (-a * (t - τ) / 2) * (C * Real.exp (-(2 + a) * τ / 2)) :=
        mul_le_mul_of_nonneg_left (hbound τ hτ) (Real.exp_pos _).le
      _ = C * Real.exp (-a * t / 2) * Real.exp (-τ) := by
        have he : Real.exp (-a * (t - τ) / 2) * Real.exp (-(2 + a) * τ / 2) =
            Real.exp (-a * t / 2) * Real.exp (-τ) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          _ = C * (Real.exp (-a * (t - τ) / 2) * Real.exp (-(2 + a) * τ / 2)) := by ring
          _ = _ := by rw [he]; ring
  rw [integral_const_mul, integral_exp_neg_Icc t ht] at hi
  exact hi.trans (mul_le_of_le_one_right (mul_nonneg hC (Real.exp_pos _).le)
    (by linarith [Real.exp_pos (-t)]))

end DefocusingNLS

end OAI
