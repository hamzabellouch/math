import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing
namespace ScaleData

section

variable (d : ScaleData)

lemma C_pos : 0 < d.C := by
  unfold C
  omega

lemma one_le_C : 1 ≤ d.C := d.C_pos

lemma L_zero_le_C : d.L 0 ≤ d.C := by
  unfold C
  omega

lemma slope_le_C : 1 + 2 * d.rA ≤ d.C := by
  unfold C
  omega

lemma L_eq (n : ℕ) : d.L n = d.L 0 + (1 + 2 * d.rA) * n := by
  simp only [L]
  ring

lemma L_le (n : ℕ) : d.L n ≤ d.C * (n + 1) := by
  rw [d.L_eq]
  have := Nat.mul_le_mul_right n d.slope_le_C
  nlinarith [d.L_zero_le_C]

lemma power_square_lower (n : ℕ) : 16 * (n + 1) ≤ 2 ^ ((n + 2) ^ 2) := by
  have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h₂ : n + 4 ≤ (n + 2) ^ 2 := by nlinarith
  calc
    16 * (n + 1) ≤ 16 * 2 ^ n := Nat.mul_le_mul_left _ h₁
    _ = 2 ^ (n + 4) := by rw [pow_add]; norm_num; ring
    _ ≤ 2 ^ ((n + 2) ^ 2) := Nat.pow_le_pow_right (by decide) h₂

lemma s_lower (n : ℕ) : 16 * d.C * (n + 1) ≤ d.s n := by
  unfold s
  have := Nat.mul_le_mul_left d.C (power_square_lower n)
  nlinarith

lemma C_le_s (n : ℕ) : d.C ≤ d.s n := by
  have := d.s_lower n
  nlinarith

lemma s_pos (n : ℕ) : 0 < d.s n := lt_of_lt_of_le d.C_pos (d.C_le_s n)

lemma sixteen_le_s (n : ℕ) : 16 ≤ d.s n := by
  have := d.s_lower n
  have := d.one_le_C
  nlinarith

lemma s_mono : Monotone d.s := by
  intro j n hjn
  exact Nat.mul_le_mul_left d.C
    (Nat.pow_le_pow_right (by decide) (by nlinarith : (j + 2) ^ 2 ≤ (n + 2) ^ 2))

lemma s_succ (n : ℕ) : d.s (n + 1) = 2 ^ (2 * n + 5) * d.s n := by
  unfold s
  have : (n + 1 + 2) ^ 2 = (2 * n + 5) + (n + 2) ^ 2 := by ring
  rw [this, pow_add]
  ring

lemma s_succ_lower (n : ℕ) : 32 * (n + 1) * d.s n ≤ d.s (n + 1) := by
  have h₁ : n + 1 ≤ 2 ^ (2 * n) :=
    le_trans (Nat.lt_two_pow_self (n := n))
      (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2 * n))
  have h₂ : 32 * (n + 1) ≤ 2 ^ (2 * n + 5) := by
    rw [pow_add]
    norm_num
    nlinarith
  rw [d.s_succ]
  exact Nat.mul_le_mul_right _ h₂

lemma small_motion_exponents (n : ℕ) :
    (n + 10) * d.s n + d.L (n + 1) ≤ d.s (n + 1) := by
  have hL : d.L (n + 1) ≤ (n + 2) * d.s n := by
    have h := d.L_le (n + 1)
    have h' := Nat.mul_le_mul_right (n + 2) (d.C_le_s n)
    nlinarith
  have hS := d.s_succ_lower n
  nlinarith

lemma old_record_exponents {j n : ℕ} (hjn : j < n) : d.s j + d.L n ≤ d.s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hjk : j ≤ k := by omega
  have hs := d.s_mono hjk
  have hL : d.L (k + 1) ≤ (k + 2) * d.s k := by
    have h := d.L_le (k + 1)
    have h' := Nat.mul_le_mul_right (k + 2) (d.C_le_s k)
    nlinarith
  have hS := d.s_succ_lower k
  nlinarith

lemma L_le_s (n : ℕ) : d.L n ≤ d.s n := by
  have := d.L_le n
  have := d.s_lower n
  nlinarith

lemma memory_exponents (n : ℕ) : 15 * (n + 1) + d.L n ≤ d.s n := by
  have := d.L_le n
  have := d.s_lower n
  have := d.one_le_C
  nlinarith

lemma capacity_pos (n : ℕ) : 0 < d.capacity n := by
  exact pow_pos (by decide) _

lemma D_pos (n : ℕ) : 0 < d.D n := by
  exact pow_pos (by decide) _

lemma delta_pos (n : ℕ) : 0 < d.δ n := by
  unfold δ
  positivity

lemma delta_nonneg (n : ℕ) : 0 ≤ d.δ n := (d.delta_pos n).le

lemma delta_le_one (n : ℕ) : d.δ n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma delta_eq_inv_D (n : ℕ) : d.δ n = (d.D n : ℝ)⁻¹ := by
  simp [δ, D, one_div, inv_pow]

lemma delta_capacity (n : ℕ) :
    d.δ n * (d.capacity n : ℝ) = (1 / 2 : ℝ) ^ (d.s n - d.L n) := by
  have hs : d.s n = (d.s n - d.L n) + d.L n :=
    (Nat.sub_add_cancel (d.L_le_s n)).symm
  unfold δ capacity
  rw [hs, pow_add]
  push_cast
  rw [mul_assoc, ← mul_pow]
  norm_num

lemma delta_capacity_le (n : ℕ) :
    d.δ n * (d.capacity n : ℝ) ≤ (1 / 2 : ℝ) ^ (15 * (n + 1)) := by
  rw [d.delta_capacity]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := d.memory_exponents n
  omega

lemma delta_le_sixteen (n : ℕ) : d.δ n ≤ (1 / 2 : ℝ) ^ 16 := by
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (d.sixteen_le_s n)

lemma delta_lt_one (n : ℕ) : d.δ n < 1 := by
  have := d.delta_le_sixteen n
  norm_num at this ⊢
  linarith

lemma delta_le_geometric (n : ℕ) : d.δ n ≤ (1 / 2 : ℝ) ^ n := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := d.s_lower n
  have := d.one_le_C
  nlinarith

lemma b_pos (n : ℕ) : 0 < d.b n := by
  exact mul_pos (d.delta_pos _) (Nat.cast_pos.mpr (d.capacity_pos _))

lemma b_le_delta_pow (n : ℕ) : d.b n ≤ d.δ n ^ (n + 10) := by
  unfold b
  rw [d.delta_capacity, δ, ← pow_mul]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := d.small_motion_exponents n
  rw [Nat.mul_comm (d.s n)]
  omega

lemma b_lt_delta_div_eight (n : ℕ) : d.b n < d.δ n / 8 := by
  have h₁ : d.δ n ^ (n + 10) ≤ d.δ n ^ 2 :=
    pow_le_pow_of_le_one (d.delta_nonneg n) (d.delta_le_one n) (by omega)
  have hδ : d.δ n < 1 / 8 := by
    have := d.delta_le_sixteen n
    norm_num at this ⊢
    linarith
  have h₂ : d.δ n ^ 2 < d.δ n / 8 := by
    have h := mul_lt_mul_of_pos_left hδ (d.delta_pos n)
    nlinarith
  exact lt_of_le_of_lt (le_trans (d.b_le_delta_pow n) h₁) h₂

lemma capacity_dvd_old_weight {j n : ℕ} (hjn : j < n) :
    d.capacity n ∣ 2 ^ (d.s n - d.s j) := by
  apply Nat.pow_dvd_pow
  have := d.old_record_exponents hjn
  omega

lemma delta_ratio {j n : ℕ} (hjn : j ≤ n) :
    d.δ j / d.δ n = ((2 ^ (d.s n - d.s j) : ℕ) : ℝ) := by
  have hs : d.s n = (d.s n - d.s j) + d.s j :=
    (Nat.sub_add_cancel (d.s_mono hjn)).symm
  have hp : (2 : ℝ) ^ d.s j ≠ 0 := by positivity
  have hp' : (2 : ℝ) ^ (d.s n - d.s j) ≠ 0 := by positivity
  unfold δ
  simp only [one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [hs, pow_add]
  field_simp
  simp

end


lemma memory_majorant_eq (n : ℕ) :
    (1 / 2 : ℝ) ^ (15 * (n + 1)) = ((1 / 2 : ℝ) ^ 15) ^ n * (1 / 2 : ℝ) ^ 15 := by
  rw [pow_mul, pow_succ]

lemma memory_majorant_summable :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (15 * (n + 1))) := by
  simp_rw [memory_majorant_eq]
  exact (summable_geometric_of_lt_one
      (r := (1 / 2 : ℝ) ^ 15) (by positivity) (by norm_num)).mul_right ((1 / 2 : ℝ) ^ 15)

lemma memory_majorant_sum :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (15 * (n + 1))) = 1 / 32767 := by
  simp_rw [memory_majorant_eq]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) (by norm_num)]
  norm_num

variable (d : ScaleData)

lemma memory_summable : Summable (fun n => d.δ n * (d.capacity n : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (d.delta_nonneg n) (Nat.cast_nonneg _))
    (d.delta_capacity_le)
  exact memory_majorant_summable

lemma total_memory_le :
    (∑' n : ℕ, d.δ n * (d.capacity n : ℝ)) ≤ 1 / 32767 := by
  rw [← memory_majorant_sum]
  exact Summable.tsum_le_tsum d.delta_capacity_le d.memory_summable memory_majorant_summable

lemma total_memory_lt_one : (∑' n : ℕ, d.δ n * (d.capacity n : ℝ)) < 1 := by
  have := d.total_memory_le
  linarith

def addressIndex (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), 2 ^ (d.s n - d.s j) * k j

noncomputable def history (k : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), d.δ j * (k j : ℝ)

lemma history_nonneg (k : ℕ → ℕ) (n : ℕ) : 0 ≤ d.history k n := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (d.delta_nonneg j) (Nat.cast_nonneg _)

lemma history_lt_one (k : ℕ → ℕ) (n : ℕ)
    (hk : ∀ j ≤ n, k j < d.capacity j) : d.history k n < 1 := by
  calc
    d.history k n ≤ ∑ j ∈ Finset.range (n + 1), d.δ j * (d.capacity j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (d.delta_nonneg j)
      exact_mod_cast (hk j (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj)).le
    _ ≤ ∑' j : ℕ, d.δ j * (d.capacity j : ℝ) := by
      apply Summable.sum_le_tsum
      · intro j _
        exact mul_nonneg (d.delta_nonneg j) (Nat.cast_nonneg _)
      · exact d.memory_summable
    _ < 1 := d.total_memory_lt_one

lemma history_eq_address (k : ℕ → ℕ) (n : ℕ) :
    d.history k n = (d.addressIndex k n : ℝ) * d.δ n := by
  unfold history addressIndex
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
  have h := (div_eq_iff (d.delta_pos n).ne').mp (d.delta_ratio hjn)
  rw [h]
  push_cast
  ring

lemma address_lt_D (k : ℕ → ℕ) (n : ℕ)
    (hk : ∀ j ≤ n, k j < d.capacity j) : d.addressIndex k n < d.D n := by
  have hy := d.history_lt_one k n hk
  rw [d.history_eq_address, d.delta_eq_inv_D, ← div_eq_mul_inv] at hy
  have hD : (0 : ℝ) < (d.D n : ℝ) := Nat.cast_pos.mpr (d.D_pos n)
  exact_mod_cast (div_lt_one hD).mp hy

lemma address_mod_capacity (k : ℕ → ℕ) (n : ℕ)
    (hk : k n < d.capacity n) : d.addressIndex k n % d.capacity n = k n := by
  unfold addressIndex
  rw [Finset.sum_range_succ]
  have hdiv : d.capacity n ∣ ∑ j ∈ Finset.range n, 2 ^ (d.s n - d.s j) * k j := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left (d.capacity_dvd_old_weight (Finset.mem_range.mp hj)) _
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.mod_eq_of_lt hk]
  simp [Nat.mod_eq_of_lt hk]

theorem read_newest_record (k : ℕ → ℕ) (n : ℕ)
    (hk : ∀ j ≤ n, k j < d.capacity j) :
    ∃ m : ℕ, m < d.D n ∧ 0 ≤ d.history k n ∧ d.history k n < 1 ∧
      d.history k n = (m : ℝ) * d.δ n ∧ m % d.capacity n = k n := by
  exact ⟨d.addressIndex k n, d.address_lt_D k n hk,
    d.history_nonneg k n, d.history_lt_one k n hk,
    d.history_eq_address k n, d.address_mod_capacity k n (hk n le_rfl)⟩

end ScaleData
end RapidForcing

end OAI
