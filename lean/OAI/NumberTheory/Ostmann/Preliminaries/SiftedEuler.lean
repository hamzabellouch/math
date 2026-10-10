import OAI.NumberTheory.Ostmann.Preliminaries.SiftedWeights

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

theorem local_log_lower {j p : ℝ} (hj : 0 ≤ j) (hp : j < p) :
    j/p ≤ Real.log (1+j/(p-j)) := by
  have hdiff : 0 < p-j := sub_pos.mpr hp
  have hp0 : 0 < p := lt_of_le_of_lt hj hp
  have hpos : 0 < 1+j/(p-j) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1-(1+j/(p-j))⁻¹ = j/p := by
    field_simp
    ring
  rwa [he] at h

theorem euler_product_lower (P : Finset ℕ) {j : ℝ} (hj : 0 ≤ j)
    (hP : ∀ p ∈ P, j < (p : ℝ)) :
    Real.exp (j*(∑ p ∈ P, 1/(p : ℝ))) ≤
      ∏ p ∈ P, (1+j/((p : ℝ)-j)) := by
  have hpos : ∀ p ∈ P, 0 < 1+j/((p : ℝ)-j) := by
    intro p hp
    have : 0 < (p : ℝ)-j := sub_pos.mpr (hP p hp)
    positivity
  apply (Real.le_log_iff_exp_le (Finset.prod_pos hpos)).mp
  rw [Real.log_prod (fun p hp => (hpos p hp).ne'), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  simpa only [mul_one_div] using local_log_lower hj (hP p hp)

theorem sieve_first_moment (P : Finset ℕ) {j : ℝ} (hj : 0 ≤ j)
    (hP : ∀ p ∈ P, j < (p : ℝ)) :
    (∑ p ∈ P, (j/((p : ℝ)-j))/(1+j/((p : ℝ)-j))*Real.log p) =
      j*(∑ p ∈ P, Real.log p/(p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdiff : 0 < (p : ℝ)-j := sub_pos.mpr (hP p hp)
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt hj (hP p hp)
  have he : (j/((p : ℝ)-j))/(1+j/((p : ℝ)-j)) = j/(p : ℝ) := by
    field_simp
    ring
  rw [he]
  ring

theorem log_cost_iff_product_le (t : Finset ℕ) {Q : ℕ} (hQ : 0 < Q)
    (ht : ∀ p ∈ t, 0 < p) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ) ↔ (∏ p ∈ t, p) ≤ Q := by
  have hpos : (0 : ℝ) < ∏ p ∈ t, (p : ℝ) :=
    Finset.prod_pos (fun p hp => Nat.cast_pos.mpr (ht p hp))
  rw [← Real.log_prod (s := t) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (Nat.cast_pos.mpr (ht p hp) : (0:ℝ)<p).ne'),
    Real.log_le_log_iff hpos (Nat.cast_pos.mpr hQ)]
  rw [← Nat.cast_prod]
  exact Nat.cast_le

theorem truncated_euler_lower (P : Finset ℕ) {j : ℝ} (hj : 0 ≤ j)
    (hP : ∀ p ∈ P, j < (p : ℝ)) {Q : ℕ} (hQ : 1 < Q)
    (hmean : j*(∑ p ∈ P, Real.log p/(p : ℝ)) ≤ Real.log (Q : ℝ)/2) :
    Real.exp (j*(∑ p ∈ P, 1/(p : ℝ)))/2 ≤
      ∑ t ∈ P.powerset with (∏ p ∈ t, p) ≤ Q,
        ∏ p ∈ t, j/((p : ℝ)-j) := by
  classical
  have hppos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hj (hP p hp)
  have hcost := retain_half P (fun p => j/((p : ℝ)-j)) (fun p => Real.log p)
    (L := Real.log (Q : ℝ))
    (fun p hp => div_nonneg hj (sub_pos.mpr (hP p hp)).le)
    (fun p hp => Real.log_nonneg (by exact_mod_cast hppos p hp))
    (Real.log_pos (by exact_mod_cast hQ))
    (by rwa [sieve_first_moment P hj hP])
  have heq : P.powerset.filter (fun t : Finset ℕ => (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ)) =
      P.powerset.filter (fun t : Finset ℕ => (∏ p ∈ t, p) ≤ Q) := by
    apply Finset.filter_congr
    intro t ht
    exact log_cost_iff_product_le t (by omega)
      (fun p hp => hppos p ((mem_powerset.mp ht) hp))
  rw [heq] at hcost
  exact (div_le_div_of_nonneg_right (euler_product_lower P hj hP) (by norm_num)).trans hcost

end Ostmann.SiftedWeights

end OAI
