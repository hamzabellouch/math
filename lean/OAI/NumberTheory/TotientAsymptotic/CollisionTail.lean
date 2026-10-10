import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor

namespace OAI

/-! The summable, phase-independent tail in the prefix collision estimate. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The contribution of a suffix at distance `h` from the end, after restoring
its common prefix and integrating the dyadic suffix estimates. -/
def collisionKernel (c : ℝ) (h : ℕ) : ℝ :=
  (h : ℝ)^4 * Real.exp (-c/((h : ℝ)^3*rho^h))

lemma collisionKernel_nonneg (c : ℝ) (h : ℕ) : 0 ≤ collisionKernel c h := by
  unfold collisionKernel
  positivity

lemma collisionKernel_le_geometric {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, collisionKernel c h ≤ Real.exp (-1)^h := by
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one 4 rho_pos.le rho_lt_one
  filter_upwards [ht.eventually (eventually_lt_nhds (div_pos hc (by norm_num : (0:ℝ)<5))),
    eventually_ge_atTop 1] with h hh hpos
  have hhR : (0 : ℝ) < h := by exact_mod_cast hpos
  have hden : 0 < (h : ℝ)^3*rho^h := mul_pos (pow_pos hhR _) (pow_pos rho_pos _)
  have hsave : (5 : ℝ)*h ≤ c/((h : ℝ)^3*rho^h) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hh]
  have hexp : (h : ℝ)^4 ≤ Real.exp (4*(h : ℝ)) := by
    have hh' : (h : ℝ) ≤ Real.exp (h : ℝ) := by linarith [Real.add_one_le_exp (h : ℝ)]
    calc
      _ ≤ (Real.exp (h : ℝ))^4 := pow_le_pow_left₀ hhR.le hh' _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  unfold collisionKernel
  calc
    _ ≤ Real.exp (4*(h : ℝ))*Real.exp (-5*(h : ℝ)) :=
      mul_le_mul hexp (Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hsave))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(h : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (-1)^h := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem summable_collisionKernel {c : ℝ} (hc : 0 < c) : Summable (collisionKernel c) := by
  have hg : Summable (fun h : ℕ => Real.exp (-1)^h) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by simp)
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [collisionKernel_le_geometric hc] with h hh
  simpa only [Real.norm_eq_abs, abs_of_nonneg (collisionKernel_nonneg c h)] using hh

def collisionTail (c : ℝ) (H : ℕ) : ℝ := ∑' n : ℕ, collisionKernel c (H+n)

lemma collisionTail_nonneg (c : ℝ) (H : ℕ) : 0 ≤ collisionTail c H :=
  tsum_nonneg (fun _ => collisionKernel_nonneg _ _)

/-- The final error can be chosen independently of the phase and tends to zero. -/
theorem collisionTail_tendsto (c : ℝ) : Tendsto (collisionTail c) atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, collisionKernel c (H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using (_root_.tendsto_sum_nat_add (collisionKernel c))

end TotientAsymptotic

end

end OAI
