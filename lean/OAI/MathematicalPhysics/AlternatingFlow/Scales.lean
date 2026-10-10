import OAI.MathematicalPhysics.AlternatingFlow.Model

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Scales

def K (N n : ℕ) : ℕ := N + 2 * n + 2

def s (N n : ℕ) : ℕ := (N + 1) * 2 ^ ((n + 3) ^ 2)

noncomputable def ε (b N n : ℕ) : ℝ := ((b : ℝ) ^ s N n)⁻¹

lemma exponent_succ (n : ℕ) : (n + 1 + 3) ^ 2 = (n + 3) ^ 2 + (2 * n + 7) := by
  ring

lemma s_succ (N n : ℕ) : s N (n + 1) = 2 ^ (2 * n + 7) * s N n := by
  simp only [s, exponent_succ, pow_add]
  ring

lemma pow_lower (n : ℕ) : 8 * (n + 1) ≤ 2 ^ ((n + 3) ^ 2) := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have he : n + 3 ≤ (n + 3) ^ 2 := by nlinarith
  calc
    8 * (n + 1) ≤ 8 * 2 ^ n := Nat.mul_le_mul_left 8 h
    _ = 2 ^ (n + 3) := by simp [pow_add]; ring
    _ ≤ 2 ^ ((n + 3) ^ 2) := Nat.pow_le_pow_right (by decide) he

lemma s_lower (N n : ℕ) : 8 * (N + 1) * (n + 1) ≤ s N n := by
  have h := Nat.mul_le_mul_left (N + 1) (pow_lower n)
  simpa only [s, mul_left_comm, mul_assoc] using h

lemma capacity_lt (N n : ℕ) : 1 + 2 * K N n < s N n := by
  have h := s_lower N n
  dsimp [K]
  nlinarith

lemma K_add_one_lt (N n : ℕ) : K N n + 1 < s N n := by
  have := capacity_lt N n
  omega

lemma s_pos (N n : ℕ) : 0 < s N n := by
  unfold s
  positivity

lemma strictMono_s (N : ℕ) : StrictMono (s N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [s_succ]
  have hp : 1 < 2 ^ (2 * n + 7) := one_lt_pow₀ (by decide) (by omega)
  nlinarith [s_pos N n]

lemma scale_gap (N n : ℕ) : s N n + 1 + 2 * K N n < s N (n + 1) := by
  rw [s_succ]
  have hc := capacity_lt N n
  have hp : 2 ≤ 2 ^ (2 * n + 7) := by
    exact Nat.le_pow (by omega)
  nlinarith [s_pos N n]

lemma old_scale_gap (N j n : ℕ) (hjn : j < n) :
    s N j + (1 + 2 * K N j) ≤ s N n := by
  have h₁ := scale_gap N j
  have h₂ := (strictMono_s N).monotone (Nat.succ_le_of_lt hjn)
  simp only [Nat.succ_eq_add_one] at h₂
  omega

lemma derivative_gap (N r n : ℕ) (hn : r ≤ n) :
    s N n + (r + 1) * (s N n + 1 + K N n) ≤ s N (n + 1) := by
  have hk := K_add_one_lt N n
  have hp : 2 * r + 3 ≤ 2 ^ (2 * n + 7) := by
    have ht : 2 * n + 7 < 2 ^ (2 * n + 7) := Nat.lt_two_pow_self
    omega
  rw [s_succ]
  nlinarith

lemma s_zero_add (N n : ℕ) : s N 0 + n ≤ s N n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := strictMono_s N (Nat.lt_succ_self n)
    simp only [Nat.succ_eq_add_one] at *
    omega

lemma n_le_s (N n : ℕ) : n ≤ s N n := by
  have := s_zero_add N n
  omega

lemma ε_pos (b N n : ℕ) (hb : 0 < b) : 0 < ε b N n := by
  unfold ε
  positivity

lemma ε_nonneg (b N n : ℕ) (hb : 0 < b) : 0 ≤ ε b N n :=
  (ε_pos b N n hb).le

lemma ε_strictAnti (b N : ℕ) (hb : 1 < b) : StrictAnti (ε b N) := by
  intro n m hnm
  unfold ε
  apply inv_strictAnti₀ _ _
  · positivity
  · exact pow_lt_pow_right₀ (by exact_mod_cast hb) (strictMono_s N hnm)

lemma ε_le_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold ε
  rw [one_div, inv_pow]
  apply inv_anti₀ (by positivity)
  calc
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ s N n := pow_le_pow_right₀ (by norm_num) (n_le_s N n)
    _ ≤ (b : ℝ) ^ s N n := pow_le_pow_left₀ (by norm_num) hb' _

lemma ε_le_initial_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ ε b N 0 * (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N n := by
    calc
      (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N 0 * (b : ℝ) ^ n := by
        gcongr
      _ = (b : ℝ) ^ (s N 0 + n) := (pow_add _ _ _).symm
      _ ≤ (b : ℝ) ^ s N n := pow_le_pow_right₀ (by linarith) (s_zero_add N n)
  simpa only [ε, one_div, inv_pow, mul_inv_rev, mul_comm] using
    (inv_anti₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ s N 0 * 2 ^ n) hp)

lemma summable_ε (b N : ℕ) (hb : 2 ≤ b) : Summable (ε b N) := by
  exact Summable.of_nonneg_of_le
    (fun n => ε_nonneg b N n (by omega))
    (fun n => ε_le_geometric b N n hb) summable_geometric_two

lemma total_memory_le (b N : ℕ) (hb : 2 ≤ b) :
    (∑' n : ℕ, ε b N n) ≤ 2 * ε b N 0 := by
  have hg := summable_geometric_two.mul_left (ε b N 0)
  have h := (summable_ε b N hb).tsum_le_tsum
    (fun n => ε_le_initial_geometric b N n hb) hg
  calc
    (∑' n : ℕ, ε b N n) ≤ ∑' n : ℕ, ε b N 0 * (1 / 2 : ℝ) ^ n := h
    _ = 2 * ε b N 0 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

lemma initial_memory_small (b N : ℕ) (hb : 4 ≤ b) : 2 * ε b N 0 < 1 / 4 := by
  have hs : 2 ≤ s N 0 := by have := s_lower N 0; nlinarith
  have hb' : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (16 : ℝ) ≤ (b : ℝ) ^ s N 0 := by
    calc
      (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ (4 : ℝ) ^ s N 0 := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ (b : ℝ) ^ s N 0 := pow_le_pow_left₀ (by norm_num) hb' _
  have hε : ε b N 0 ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
  norm_num at hε
  linarith

lemma derivative_cost_bound (b N r n : ℕ) (hb : 2 ≤ b) (hn : r ≤ n) :
    ε b N (n + 1) * (b : ℝ) ^ ((r + 1) * (s N n + 1 + K N n)) ≤ ε b N n := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have h := pow_le_pow_right₀ hb' (derivative_gap N r n hn)
  have hpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  dsimp [ε]
  rw [← div_eq_inv_mul, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).2
  simpa [pow_add, mul_comm] using h

lemma summable_weighted_ε (b N J : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n) := by
  have h₀ := summable_pow_mul_geometric_of_norm_lt_one J
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h₁ := ((summable_nat_add_iff 1).2 h₀).mul_left (2 : ℝ)
  have h₂ : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * (1 / 2 : ℝ) ^ n) := by
    apply h₁.congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (ε_nonneg b N n (by omega)))
    (fun n => mul_le_mul_of_nonneg_left (ε_le_geometric b N n hb) (by positivity)) h₂

lemma weighted_ε_tendsto_zero (b N J : ℕ) (hb : 2 ≤ b) :
    Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n)
      Filter.atTop (𝓝 0) :=
  (summable_weighted_ε b N J hb).tendsto_atTop_zero

lemma weighted_ε_bounded (b N J : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n ≤ C := by
  refine ⟨∑' n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n, ?_, ?_⟩
  · apply tsum_nonneg
    intro n
    exact mul_nonneg (by positivity) (ε_nonneg b N n (by omega))
  · intro n
    apply (summable_weighted_ε b N J hb).le_tsum
    intro j _
    exact mul_nonneg (by positivity) (ε_nonneg b N j (by omega))

end Scales
end AlternatingNS

end OAI
