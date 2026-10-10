import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating.Memory
open scoped BigOperators
open Finset

def width (N n : ℕ) : ℕ := N + 2 * n + 2

def scale (N n : ℕ) : ℕ := (N + 1) * 2 ^ ((n + 3) ^ 2)

noncomputable def epsilon (b N n : ℕ) : ℝ := (b : ℝ)⁻¹ ^ scale N n

theorem scale_succ (N n : ℕ) :
    scale N (n + 1) = 2 ^ (2 * n + 7) * scale N n := by
  unfold scale
  have h : (n + 1 + 3) ^ 2 = (n + 3) ^ 2 + (2 * n + 7) := by ring
  rw [h, pow_add]
  ring

theorem exponent_linear_lower (n : ℕ) :
    8 * (n + 1) ≤ 2 ^ ((n + 3) ^ 2) := by
  calc
    8 * (n + 1) ≤ 8 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt n.lt_two_pow_self)
    _ = 2 ^ (n + 3) := by rw [pow_add]; norm_num; omega
    _ ≤ 2 ^ ((n + 3) ^ 2) := Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem scale_above_block (N n : ℕ) : 1 + 2 * width N n < scale N n := by
  have h := Nat.mul_le_mul_left (N + 1) (exponent_linear_lower n)
  dsimp [scale, width]
  nlinarith

theorem scale_pos (N n : ℕ) : 0 < scale N n := by
  unfold scale
  positivity

theorem ratio_lower (n : ℕ) : 128 * (n + 1) ≤ 2 ^ (2 * n + 7) := by
  calc
    128 * (n + 1) ≤ 128 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt n.lt_two_pow_self)
    _ = 2 ^ (n + 7) := by rw [pow_add]; norm_num; omega
    _ ≤ 2 ^ (2 * n + 7) := Nat.pow_le_pow_right (by decide) (by omega)

theorem twice_scale_le_succ (N n : ℕ) : 2 * scale N n ≤ scale N (n + 1) := by
  rw [scale_succ]
  exact Nat.mul_le_mul_right _ (by have := ratio_lower n; omega)

theorem scale_strictMono (N : ℕ) : StrictMono (scale N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := twice_scale_le_succ N n
  have := scale_pos N n
  omega

theorem scale_succ_gap (N n : ℕ) :
    scale N n + 1 + 2 * width N n < scale N (n + 1) := by
  have := scale_above_block N n
  have := twice_scale_le_succ N n
  omega

theorem old_block_gap (N : ℕ) {j n : ℕ} (h : j < n) :
    scale N j + 1 + 2 * width N j < scale N n :=
  (scale_succ_gap N j).trans_le ((scale_strictMono N).monotone (by omega))

theorem index_le_scale (N n : ℕ) : n ≤ scale N n := by
  have := scale_above_block N n
  dsimp [width] at this
  omega

theorem derivative_budget (N r n : ℕ) (h : r ≤ n) :
    scale N n + (r + 1) * (scale N n + 1 + width N n) ≤ scale N (n + 1) := by
  have hk : 1 + width N n ≤ scale N n := by
    have := scale_above_block N n
    omega
  have hr : 2 * r + 3 ≤ 2 ^ (2 * n + 7) := by
    have := ratio_lower n
    omega
  calc
    _ ≤ scale N n + (r + 1) * (2 * scale N n) := by gcongr; omega
    _ = (2 * r + 3) * scale N n := by ring
    _ ≤ 2 ^ (2 * n + 7) * scale N n := Nat.mul_le_mul_right _ hr
    _ = _ := (scale_succ N n).symm

theorem epsilon_pos {b : ℕ} (hb : 0 < b) (N n : ℕ) : 0 < epsilon b N n := by
  unfold epsilon
  positivity

theorem epsilon_nonneg {b : ℕ} (hb : 0 < b) (N n : ℕ) : 0 ≤ epsilon b N n :=
  (epsilon_pos hb N n).le

theorem epsilon_succ_le {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    epsilon b N (n + 1) ≤ epsilon b N n * (b : ℝ)⁻¹ := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hbase : (b : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
  have h := pow_le_pow_of_le_one (by positivity : 0 ≤ (b : ℝ)⁻¹) hbase
    (Nat.succ_le_of_lt (scale_strictMono N (Nat.lt_succ_self n)))
  simpa [epsilon, pow_succ] using h

theorem epsilon_succ_half {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    2 * epsilon b N (n + 1) ≤ epsilon b N n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hinv : (b : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hb')
  have h := (epsilon_succ_le hb N n).trans
    (mul_le_mul_of_nonneg_left hinv (epsilon_nonneg (by omega) N n))
  linarith

theorem epsilon_strictAnti {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    StrictAnti (epsilon b N) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have := epsilon_succ_half hb N n
  have := epsilon_pos (by omega : 0 < b) N (n + 1)
  linarith

theorem epsilon_sum_range {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    ∑ j ∈ range n, epsilon b N j ≤ 2 * epsilon b N 0 - 2 * epsilon b N n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have := epsilon_succ_half hb N n
    linarith

theorem epsilon_sum_range_le {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    ∑ j ∈ range n, epsilon b N j ≤ 2 * epsilon b N 0 := by
  have := epsilon_sum_range hb N n
  have := epsilon_pos (by omega : 0 < b) N n
  linarith

theorem epsilon_summable {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    Summable (epsilon b N) :=
  summable_of_sum_range_le (fun n => epsilon_nonneg (by omega) N n)
    (epsilon_sum_range_le hb N)

theorem epsilon_tsum_le {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    ∑' n, epsilon b N n ≤ 2 * epsilon b N 0 :=
  (epsilon_summable hb N).tsum_le_of_sum_range_le (epsilon_sum_range_le hb N)

theorem initial_epsilon_small {b : ℕ} (hb : 4 ≤ b) (N : ℕ) :
    2 * epsilon b N 0 < 1 / 4 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hb4 : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : 2 ≤ scale N 0 := by have := scale_above_block N 0; dsimp [width] at this; omega
  have h1 := pow_le_pow_of_le_one (by positivity : 0 ≤ (b : ℝ)⁻¹)
    (inv_le_one_of_one_le₀ hb1) hs
  have hbase : (b : ℝ)⁻¹ ≤ 1 / 4 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hb4
  have h2 : (b : ℝ)⁻¹ ^ 2 ≤ (1 / 16 : ℝ) := by
    calc
      _ ≤ (1 / 4 : ℝ) ^ 2 := by gcongr
      _ = _ := by norm_num
  change 2 * (b : ℝ)⁻¹ ^ scale N 0 < 1 / 4
  linarith

theorem epsilon_tsum_small {b : ℕ} (hb : 4 ≤ b) (N : ℕ) :
    ∑' n, epsilon b N n < 1 / 4 :=
  (epsilon_tsum_le (by omega) N).trans_lt (initial_epsilon_small hb N)

theorem derivative_cost_absorbed {b : ℕ} (hb : 2 ≤ b) (N r n : ℕ) (hn : r ≤ n) :
    epsilon b N (n + 1) * (b : ℝ) ^ ((r + 1) * (scale N n + 1 + width N n)) ≤
      epsilon b N n := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hpow := pow_le_pow_right₀ hb1 (derivative_budget N r n hn)
  rw [pow_add] at hpow
  have hdiv :
      (b : ℝ) ^ ((r + 1) * (scale N n + 1 + width N n)) / (b : ℝ) ^ scale N (n + 1) ≤
        1 / (b : ℝ) ^ scale N n := by
    apply (div_le_div_iff₀ (pow_pos hbpos _) (pow_pos hbpos _)).2
    simpa [mul_comm] using hpow
  simpa [epsilon, inv_pow, div_eq_mul_inv, mul_comm] using hdiv

theorem epsilon_le_geometric {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    epsilon b N n ≤ (1 / 2 : ℝ) ^ n := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : (b : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hb2
  calc
    epsilon b N n ≤ (b : ℝ)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hb1) (index_le_scale N n)
    _ ≤ _ := by gcongr

theorem weighted_geometric_summable (J : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ J * (1 / 2 : ℝ) ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one J
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hs : Summable (fun n : ℕ => ((n + 3 : ℕ) : ℝ) ^ J * (1 / 2 : ℝ) ^ (n + 3)) :=
    h.comp_injective (fun _ _ h => by omega)
  have heq : (fun n : ℕ => ((n : ℝ) + 3) ^ J * (1 / 2 : ℝ) ^ n) =
      (fun n : ℕ => (((n + 3 : ℕ) : ℝ) ^ J * (1 / 2 : ℝ) ^ (n + 3)) * 8) := by
    funext n
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [heq]
  exact hs.mul_right 8

theorem weighted_epsilon_summable {b : ℕ} (hb : 2 ≤ b) (N J : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ J * epsilon b N n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (epsilon_nonneg (by omega : 0 < b) N n))
    (fun n => mul_le_mul_of_nonneg_left (epsilon_le_geometric hb N n) (by positivity))
    (weighted_geometric_summable J)

theorem weighted_epsilon_bounded {b : ℕ} (hb : 2 ≤ b) (N J : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 3) ^ J * epsilon b N n ≤ C := by
  refine ⟨∑' n : ℕ, ((n : ℝ) + 3) ^ J * epsilon b N n, ?_⟩
  intro n
  apply (weighted_epsilon_summable hb N J).le_tsum n
  intro i _hi
  exact mul_nonneg (by positivity) (epsilon_nonneg (by omega) N i)

end Alternating.Memory

namespace Alternating.Memory
open scoped BigOperators

noncomputable def slotMajorant (b N r n : ℕ) : ℝ :=
  epsilon b N n +
    epsilon b N (n + 1) * (b : ℝ) ^ ((r + 1) * (scale N n + 1 + width N n))

theorem slotMajorant_nonneg {b : ℕ} (hb : 2 ≤ b) (N r n : ℕ) :
    0 ≤ slotMajorant b N r n := by
  unfold slotMajorant
  exact add_nonneg (epsilon_nonneg (by omega) N n)
    (mul_nonneg (epsilon_nonneg (by omega) N (n + 1)) (by positivity))

theorem slotMajorant_tail {b : ℕ} (hb : 2 ≤ b) (N r n : ℕ) (hn : r ≤ n) :
    slotMajorant b N r n ≤ 2 * epsilon b N n := by
  have := derivative_cost_absorbed hb N r n hn
  dsimp [slotMajorant]
  linarith

theorem weighted_slotMajorant_bounded {b : ℕ} (hb : 2 ≤ b) (N r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ((n : ℝ) + 3) ^ J * slotMajorant b N r n ≤ C := by
  obtain ⟨B, hB⟩ := weighted_epsilon_bounded hb N J
  have hB0 : 0 ≤ B :=
    (mul_nonneg (by positivity) (epsilon_nonneg (by omega) N 0)).trans (hB 0)
  let A := ∑ n ∈ Finset.range r, ((n : ℝ) + 3) ^ J * slotMajorant b N r n
  have hA : 0 ≤ A := Finset.sum_nonneg fun n _ =>
    mul_nonneg (by positivity) (slotMajorant_nonneg hb N r n)
  refine ⟨A + 2 * B, by positivity, fun n => ?_⟩
  by_cases hn : r ≤ n
  · have hn' := mul_le_mul_of_nonneg_left (slotMajorant_tail hb N r n hn)
      (by positivity : 0 ≤ ((n : ℝ) + 3) ^ J)
    have hnB := hB n
    nlinarith
  · have hsum : ((n : ℝ) + 3) ^ J * slotMajorant b N r n ≤ A := by
      change _ ≤ ∑ j ∈ Finset.range r, ((j : ℝ) + 3) ^ J * slotMajorant b N r j
      apply Finset.single_le_sum (f := fun j : ℕ => ((j : ℝ) + 3) ^ J * slotMajorant b N r j)
      · intro j _
        exact mul_nonneg (by positivity) (slotMajorant_nonneg hb N r j)
      · exact Finset.mem_range.2 (by omega)
    linarith

end Alternating.Memory

end OAI
