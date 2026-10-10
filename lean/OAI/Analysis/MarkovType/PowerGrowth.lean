import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter

namespace MarkovSuperreflexivity

theorem not_forall_power_le_linear {p c A : ℝ} (hp : 1 < p) (hc : 0 < c) :
    ¬ ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ p ≤ A * (n : ℝ) := by
  intro hbound
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hlarge⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hlim.eventually_gt_atTop (A / c))).exists
  have hnpos : 0 < (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpower : (n : ℝ) ^ p = (n : ℝ) ^ (p - 1) * (n : ℝ) := by
    calc
      (n : ℝ) ^ p = (n : ℝ) ^ ((p - 1) + 1) := by congr 1 ; ring
      _ = (n : ℝ) ^ (p - 1) * (n : ℝ) := by
        rw [Real.rpow_add hnpos, Real.rpow_one]
  have hsmall : c * (n : ℝ) ^ (p - 1) ≤ A := by
    apply (mul_le_mul_iff_of_pos_right hnpos).mp
    simpa only [hpower, mul_assoc] using hbound n hn
  have hstrict : A < (n : ℝ) ^ (p - 1) * c := (div_lt_iff₀ hc).mp hlarge
  exact (not_lt_of_ge (by simpa only [mul_comm] using hsmall)) hstrict

theorem not_all_walk_moment_bounds {p K : ℝ} (hp : 1 < p) :
    ¬ ∀ n : ℕ, 1 ≤ n →
      (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤ K ^ p * (n : ℝ) := by
  intro hbound
  apply not_forall_power_le_linear (c := (3 / 20 : ℝ) / (24 : ℝ) ^ p)
    (A := K ^ p) hp (div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) p))
  intro n hn
  calc
    ((3 / 20 : ℝ) / (24 : ℝ) ^ p) * (n : ℝ) ^ p =
        (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p := by
      rw [Real.div_rpow (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 24) p]
      ring
    _ ≤ K ^ p * (n : ℝ) := hbound n hn

end MarkovSuperreflexivity

end

end OAI
