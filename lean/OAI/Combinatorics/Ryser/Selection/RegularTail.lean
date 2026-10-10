import OAI.Combinatorics.Ryser.Probability.Variance
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem prob_regular_target_gt_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (D m q γ C M : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hγ : 0 < γ)
    (hmean : μ.expectation Z ≤ C * M / q)
    (hvar : μ.variance Z ≤ 2 * D ^ 7 * m * q ^ 2 +
      2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) :
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
      2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := by
  have ht : 0 < γ * m * q := mul_pos (mul_pos hγ hm) hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  calc
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
        μ.variance Z / (γ * m * q) ^ 2 :=
      μ.prob_gt_mean_bound_add_le Z (C * M / q) (γ * m * q) hmean ht
    _ ≤ (2 * D ^ 7 * m * q ^ 2 + 2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) /
        (γ * m * q) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + (2 * D ^ 5 / γ ^ 2) * (Real.sqrt q / q) := by
      field_simp [hγ.ne', hm.ne', hq.ne']
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + (2 * D ^ 5 / γ ^ 2) * (1 / Real.sqrt q) := by
      rw [Real.sqrt_div_self']
    _ = 2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := by
      field_simp [hγ.ne', hm.ne', hs.ne']

theorem regular_tail_bound_le_sqrt (D m q C γ : ℝ)
    (hD : 0 ≤ D) (hm : 0 < m) (hq : 1 ≤ q)
    (hC : 0 < C) (hγ : 0 < γ) (hlarge : q / (4 * C) < m) :
    2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) ≤
      ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
  have hs : 0 < Real.sqrt q :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hq)
  have hsle : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hg2 : 0 < γ ^ 2 := pow_pos hγ 2
  have h4C : 0 < 4 * C := mul_pos (by norm_num) hC
  have hsm : Real.sqrt q ≤ (4 * C) * m := by
    calc
      Real.sqrt q ≤ q := hsle
      _ ≤ m * (4 * C) := ((div_lt_iff₀ h4C).mp hlarge).le
      _ = (4 * C) * m := mul_comm _ _
  have hcoef : 0 ≤ 2 * D ^ 7 * γ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hD 7)) hg2.le
  have hfirst : 2 * D ^ 7 / (γ ^ 2 * m) ≤
      8 * C * D ^ 7 / (γ ^ 2 * Real.sqrt q) := by
    apply (div_le_div_iff₀ (mul_pos hg2 hm) (mul_pos hg2 hs)).mpr
    calc
      (2 * D ^ 7) * (γ ^ 2 * Real.sqrt q) =
          (2 * D ^ 7 * γ ^ 2) * Real.sqrt q := by ring
      _ ≤ (2 * D ^ 7 * γ ^ 2) * ((4 * C) * m) :=
        mul_le_mul_of_nonneg_left hsm hcoef
      _ = (8 * C * D ^ 7) * (γ ^ 2 * m) := by ring
  calc
    2 * D ^ 7 / (γ ^ 2 * m) + 2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) ≤
        8 * C * D ^ 7 / (γ ^ 2 * Real.sqrt q) +
          2 * D ^ 5 / (γ ^ 2 * Real.sqrt q) := add_le_add hfirst le_rfl
    _ = ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
      rw [← add_div, div_div]

theorem prob_regular_target_gt_le_sqrt {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (D m q γ C M : ℝ)
    (hD : 0 ≤ D) (hm : 0 < m) (hq : 1 ≤ q) (hγ : 0 < γ) (hC : 0 < C)
    (hlarge : q / (4 * C) < m)
    (hmean : μ.expectation Z ≤ C * M / q)
    (hvar : μ.variance Z ≤ 2 * D ^ 7 * m * q ^ 2 +
      2 * D ^ 5 * m ^ 2 * q * Real.sqrt q) :
    μ.prob (fun x => C * M / q + γ * m * q < Z x) ≤
      ((8 * C * D ^ 7 + 2 * D ^ 5) / γ ^ 2) / Real.sqrt q := by
  exact (prob_regular_target_gt_le μ Z D m q γ C M hm
    (lt_of_lt_of_le zero_lt_one hq) hγ hmean hvar).trans
      (regular_tail_bound_le_sqrt D m q C γ hD hm hq hC hγ hlarge)

theorem card_irregular_le {ι : Type*} (S : Finset ι) (A : ι → ℝ) (K D m q : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hsum : (∑ i ∈ S, A i) ≤ K * D * m * q ^ 2) :
    ((S.filter (fun i => m * q * Real.sqrt q < A i)).card : ℝ) ≤
      K * D * Real.sqrt q := by
  classical
  let T := S.filter (fun i => m * q * Real.sqrt q < A i)
  change (T.card : ℝ) ≤ K * D * Real.sqrt q
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have ht : 0 < m * q * Real.sqrt q := mul_pos (mul_pos hm hq) hs
  have hcount : (T.card : ℝ) * (m * q * Real.sqrt q) ≤ ∑ i ∈ T, A i := by
    simpa only [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum T A (m * q * Real.sqrt q)
        (fun i hi => (Finset.mem_filter.mp hi).2.le))
  have hsub : (∑ i ∈ T, A i) ≤ ∑ i ∈ S, A i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => hA i hi)
  have hquot : (T.card : ℝ) ≤ (K * D * m * q ^ 2) / (m * q * Real.sqrt q) :=
    (le_div_iff₀ ht).mpr (hcount.trans (hsub.trans hsum))
  calc
    (T.card : ℝ) ≤ (K * D * m * q ^ 2) / (m * q * Real.sqrt q) := hquot
    _ = K * D * (q / Real.sqrt q) := by
      field_simp [hm.ne', hq.ne', hs.ne']
    _ = K * D * Real.sqrt q := by rw [Real.div_sqrt]

end RyserCoveringCounterexample.Selection

end OAI
