import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-!
# The coefficient-vanishing steps in the invariant-tensor argument

These are the two limiting arguments in `lem:invariant-intertwiners`.
They do not assume the classification of intertwiners: the finite-stage
coefficient identities and their norm bounds still have to be constructed.
-/

noncomputable section

namespace KadisonSimilarity

open Filter
open scoped Topology

private theorem coefficient_zero_of_power_bound (m : ℕ → ℝ)
    (hm : ∀ j, 0 < m j) (hmTop : Tendsto m atTop atTop)
    {a C p q : ℝ} (hqp : q < p)
    (hbound : ∀ j, |a| * (m j) ^ p ≤ C * (m j) ^ q) : a = 0 := by
  have hle (j : ℕ) : |a| ≤ C * (m j) ^ (q - p) := by
    rw [Real.rpow_sub (hm j)]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (hm j) p)).mpr (hbound j)
  have ht : Tendsto (fun j => C * (m j) ^ (q - p)) atTop (𝓝 0) := by
    have ht₀ := (tendsto_rpow_neg_atTop (sub_pos.mpr hqp)).comp hmTop
    have hsub : q - p = -(p - q) := by ring
    rw [hsub]
    simpa using ht₀.const_mul C
  have hnonpos : |a| ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hle)
  exact abs_eq_zero.mp (le_antisymm hnonpos (abs_nonneg a))

/-- The endpoint `L¹` bound removes a stable cycle coefficient whose number
of cycles is below `1 + (k+l)/2`. Matrix sizes may run through any cofinal
sequence, as they do for the increasing matrix subalgebras in the paper. -/
theorem cycle_coefficient_zero (m : ℕ → ℝ)
    (hm : ∀ j, 0 < m j) (hmTop : Tendsto m atTop atTop)
    (k l cycles : ℕ) (a : ℂ) (C : ℝ)
    (hfew : (cycles : ℝ) < 1 + ((k : ℝ) + l) / 2)
    (hbound : ∀ j, ‖a‖ * (m j) ^ (-(cycles : ℝ)) ≤
      C * (m j) ^ (-1 - ((k : ℝ) + l) / 2)) : a = 0 := by
  have hzero : ‖a‖ = 0 := by
    apply coefficient_zero_of_power_bound m hm hmTop (by linarith :
      -1 - ((k : ℝ) + l) / 2 < -(cycles : ℝ))
    simpa only [abs_norm] using hbound
  exact norm_eq_zero.mp hzero

/-- Summing orthonormal labels removes a pairing with a source-source or
test-test pair: its coefficient grows faster than the product of vector norms. -/
theorem same_side_pairing_coefficient_zero (a : ℂ) (C : ℝ) (rSource rTest : ℕ)
    (hpair : 0 < rSource + rTest)
    (hbound : ∀ M : ℕ, 0 < M →
      ‖a‖ * (M : ℝ) ^ ((rSource + rTest : ℕ) : ℝ) ≤
        C * (M : ℝ) ^ (((rSource + rTest : ℕ) : ℝ) / 2)) : a = 0 := by
  have hr : (0 : ℝ) < rSource + rTest := by exact_mod_cast hpair
  have hmTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hzero : ‖a‖ = 0 := by
    apply coefficient_zero_of_power_bound (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
      (by intro n; positivity) hmTop (by push_cast; linarith :
        (((rSource + rTest : ℕ) : ℝ) / 2) < ((rSource + rTest : ℕ) : ℝ))
    intro n
    simpa only [abs_norm] using hbound (n + 1) (by omega)
  exact norm_eq_zero.mp hzero

end KadisonSimilarity

end

end OAI
