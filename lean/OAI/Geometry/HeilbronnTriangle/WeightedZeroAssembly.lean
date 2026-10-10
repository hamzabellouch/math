import Mathlib

namespace OAI


noncomputable section

namespace Problem355.WeightedZeroAssembly

open Finset

def caseFactor (h q : ℝ) : Fin 4 → ℝ :=
  ![1, h ^ 26 / q, h ^ 14 / q, h ^ 26 / q ^ 2]

lemma caseFactor_le_one {h q : ℝ} (hh : 1 ≤ h) (hq : h ^ 100 ≤ q)
    (i : Fin 4) : caseFactor h q i ≤ 1 := by
  have hh0 : 0 ≤ h := le_trans (by norm_num) hh
  have hq1 : 1 ≤ q := (one_le_pow₀ hh).trans hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq1
  have h26 : h ^ 26 ≤ q :=
    (pow_le_pow_right₀ hh (by norm_num : 26 ≤ 100)).trans hq
  have h14 : h ^ 14 ≤ q :=
    (pow_le_pow_right₀ hh (by norm_num : 14 ≤ 100)).trans hq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  fin_cases i
  · simp [caseFactor]
  · simpa [caseFactor] using (div_le_one hq0).mpr h26
  · simpa [caseFactor] using (div_le_one hq0).mpr h14
  · simpa [caseFactor] using
      (div_le_one (sq_pos_of_pos hq0)).mpr (h26.trans hq2)

theorem sum_le_four_mul_card_of_case_bounds
    {α κ : Type*} [Fintype κ] [DecidableEq κ] (s : Finset α)
    (shell : α → κ) (kind : α → Fin 4) (w : α → ℝ)
    (h q C U : ℝ) (hh : 1 ≤ h) (hq : h ^ 100 ≤ q)
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hcases : ∀ j i,
      (∑ a ∈ s.filter (fun a => shell a = j ∧ kind a = i), w a)
        ≤ C * U * caseFactor h q i) :
    (∑ a ∈ s, w a) ≤ 4 * (Fintype.card κ : ℝ) * C * U := by
  classical
  have hpartition :
      (∑ ji : κ × Fin 4,
        ∑ a ∈ s.filter (fun a => shell a = ji.1 ∧ kind a = ji.2), w a) =
        ∑ a ∈ s, w a := by
    simpa only [Prod.ext_iff] using
      (sum_fiberwise s (fun a => (shell a, kind a)) w)
  rw [← hpartition]
  calc
    (∑ ji : κ × Fin 4,
        ∑ a ∈ s.filter (fun a => shell a = ji.1 ∧ kind a = ji.2), w a)
      ≤ ∑ _ji : κ × Fin 4, C * U := by
        apply sum_le_sum
        intro ji _
        exact (hcases ji.1 ji.2).trans
          (by simpa using (mul_le_mul_of_nonneg_left
            (caseFactor_le_one hh hq ji.2) (mul_nonneg hC hU)))
    _ = 4 * (Fintype.card κ : ℝ) * C * U := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem sum_le_logarithmic_of_case_bounds
    {α κ : Type*} [Fintype κ] [DecidableEq κ] (s : Finset α)
    (shell : α → κ) (kind : α → Fin 4) (w : α → ℝ)
    (h q C U Cshell L : ℝ) (hh : 1 ≤ h) (hq : h ^ 100 ≤ q)
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hnumber : (Fintype.card κ : ℝ) ≤ Cshell * L)
    (hcases : ∀ j i,
      (∑ a ∈ s.filter (fun a => shell a = j ∧ kind a = i), w a)
        ≤ C * U * caseFactor h q i) :
    (∑ a ∈ s, w a) ≤ (4 * C * Cshell) * L * U := by
  apply (sum_le_four_mul_card_of_case_bounds s shell kind w h q C U
    hh hq hC hU hcases).trans
  have hm := mul_le_mul_of_nonneg_right hnumber
    (show 0 ≤ 4 * C * U by positivity)
  nlinarith

end Problem355.WeightedZeroAssembly

end

end OAI
