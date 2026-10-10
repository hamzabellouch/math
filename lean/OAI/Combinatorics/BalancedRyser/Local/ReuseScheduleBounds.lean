import Mathlib.Algebra.BigOperators.Fin
import OAI.Combinatorics.BalancedRyser.Local.ReuseScheduleAggregation

namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators
noncomputable section

abbrev Schedule (n : ℕ) := Fin n → Fin 5

def cost {n : ℕ} (A q : ℝ) (σ : Schedule n) : ℝ :=
  ∏ i, A / q ^ reuseSaving (σ i).val

def listScore (σ : List (Fin 5)) : ℕ :=
  (σ.map (fun j => reuseSaving j.val)).sum

def listCost (A q : ℝ) (σ : List (Fin 5)) : ℝ :=
  (σ.map (fun j => A / q ^ reuseSaving j.val)).prod

@[simp] theorem listScore_ofFn {n : ℕ} (σ : Schedule n) :
    listScore (List.ofFn σ) = score σ := by
  simp [listScore, score, List.map_ofFn, Fin.sum_ofFn]

@[simp] theorem listCost_ofFn {n : ℕ} (A q : ℝ) (σ : Schedule n) :
    listCost A q (List.ofFn σ) = cost A q σ := by
  simp [listCost, cost, List.map_ofFn, Fin.prod_ofFn]

theorem cost_eq {n : ℕ} (A q : ℝ) (σ : Schedule n) :
    cost A q σ = A ^ n / q ^ score σ :=
  product_extension_eq A q σ

theorem cost_le_inverse_cube {n : ℕ} (A q : ℝ) (hA : 0 ≤ A)
    (hq : 1 ≤ q) (hn : n ≤ 6) (σ : Schedule n) (hσ : 3 ≤ score σ) :
    cost A q σ ≤ (max 1 A) ^ 6 / q ^ 3 := by
  rw [cost_eq]
  exact schedule_bound_le A q hA hq hn σ hσ

theorem count_short_schedules :
    (∑ n : Fin 7, Fintype.card (Schedule n.val)) = 19531 := by
  simp only [Schedule, Fintype.card_fun, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

theorem sum_mass_le_inverse_cube (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (mass : (n : ℕ) → Schedule n → ℝ)
    (hmass : ∀ n, n ≤ 6 → ∀ σ : Schedule n,
      3 ≤ score σ → mass n σ ≤ cost A q σ) :
    (∑ n : Fin 7, ∑ σ : Schedule n.val,
      if 3 ≤ score σ then mass n.val σ else 0) ≤
        19531 * (max 1 A) ^ 6 / q ^ 3 := by
  apply sum_masses_le A q hA hq (fun n σ => mass n.val σ)
  intro n σ hσ
  simpa only [cost_eq] using hmass n.val (by omega) σ hσ

theorem inverse_cube_constant_pos (A : ℝ) :
    0 < 19531 * (max 1 A) ^ 6 := by
  exact aggregate_constant_pos A

theorem listCost_le_inverse_cube (A q : ℝ) (hA : 0 ≤ A)
    (hq : 1 ≤ q) (σ : List (Fin 5)) (hn : σ.length ≤ 6)
    (hσ : 3 ≤ listScore σ) :
    listCost A q σ ≤ (max 1 A) ^ 6 / q ^ 3 := by
  have hscore : 3 ≤ score σ.get := by
    simpa only [← listScore_ofFn, List.ofFn_get] using hσ
  have h := cost_le_inverse_cube A q hA hq hn σ.get hscore
  simpa only [← listCost_ofFn, List.ofFn_get] using h

theorem sum_list_mass_le_inverse_cube (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (mass : List (Fin 5) → ℝ)
    (hmass : ∀ σ, σ.length ≤ 6 → 3 ≤ listScore σ →
      mass σ ≤ listCost A q σ) :
    (∑ n : Fin 7, ∑ σ : Schedule n.val,
      if 3 ≤ listScore (List.ofFn σ) then mass (List.ofFn σ) else 0) ≤
        19531 * (max 1 A) ^ 6 / q ^ 3 := by
  simpa only [listScore_ofFn] using
    sum_mass_le_inverse_cube A q hA hq (fun _ σ => mass (List.ofFn σ))
      (fun n hn σ hσ => by
        simpa only [listCost_ofFn] using hmass (List.ofFn σ)
          (by simpa only [List.length_ofFn] using hn)
          (by simpa only [listScore_ofFn] using hσ))

theorem sum_high_score_le_reweighted {ι : Type*} (s : Finset ι)
    (e : ι → ℕ) (mass : ι → ℝ) (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (q : ℝ) (hq : 1 ≤ q) (m : ℕ) :
    (∑ i ∈ s, if m ≤ e i then mass i else 0) ≤
      (∑ i ∈ s, q ^ e i * mass i) / q ^ m := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with he
  · apply (le_div_iff₀ (pow_pos hq0 m)).mpr
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq he) (hmass i hi)
  · exact div_nonneg (mul_nonneg (pow_nonneg hq0.le _) (hmass i hi))
      (pow_nonneg hq0.le _)

theorem sum_high_score_masses_le {I : Fin 7 → Type*} [∀ n, Fintype (I n)]
    (e : (n : Fin 7) → I n → ℕ) (mass : (n : Fin 7) → I n → ℝ)
    (hmass : ∀ n i, 0 ≤ mass n i) (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (hweighted : ∀ n, (∑ i : I n, q ^ e n i * mass n i) ≤ (5 * A) ^ n.val) :
    (∑ n : Fin 7, ∑ i : I n, if 3 ≤ e n i then mass n i else 0) ≤
      19531 * (max 1 A) ^ 6 / q ^ 3 := by
  classical
  apply sum_length_masses_le A q hA hq
  intro n
  calc
    (∑ i : I n, if 3 ≤ e n i then mass n i else 0) ≤
        (∑ i : I n, q ^ e n i * mass n i) / q ^ 3 :=
      sum_high_score_le_reweighted Finset.univ (e n) (mass n)
        (fun i _ => hmass n i) q hq 3
    _ ≤ (5 * A) ^ n.val / q ^ 3 :=
      div_le_div_of_nonneg_right (hweighted n) (by positivity)

end
end Balanced.ReuseSchedule

end OAI
