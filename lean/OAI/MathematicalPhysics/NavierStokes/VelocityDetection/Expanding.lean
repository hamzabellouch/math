import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection.Expanding
open scoped BigOperators Topology ContDiff
open Set Function Filter

def lambda (D : ℝ) : ℝ := 4 * D

def initialRadius (ν K D : ℝ) : ℝ :=
  1024 * 3000 * (1 + ν) * lambda D * (K * D + 2)

def radius (ν K D : ℝ) (n : ℕ) : ℝ := initialRadius ν K D * lambda D ^ n

def count (K D : ℝ) (n : ℕ) : ℝ := K * D ^ n

def spacing (ν K D : ℝ) (n : ℕ) : ℝ := 16 * radius ν K D n

def duration (ν K D : ℝ) (n : ℕ) : ℝ :=
  spacing ν K D (n + 1) * (count K D (n + 1) + 2)

def startTime (ν K D : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => startTime ν K D n + duration ν K D n

private theorem lambda_pos {D : ℝ} (hD : 1 ≤ D) : 0 < lambda D := by
  dsimp [lambda]
  linarith

private theorem lambda_ge_four {D : ℝ} (hD : 1 ≤ D) : 4 ≤ lambda D := by
  dsimp [lambda]
  linarith

theorem initialRadius_lower {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    1024 * 3000 * (1 + ν) ≤ initialRadius ν K D := by
  have hl := lambda_ge_four hD
  have hkd : 0 ≤ K * D := mul_nonneg hK (by linarith)
  have hA : 0 < 1024 * 3000 * (1 + ν) := by positivity
  have hfac : 1 ≤ lambda D * (K * D + 2) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hfac hA.le
  simpa [initialRadius, mul_assoc] using h

theorem initialRadius_pos {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    0 < initialRadius ν K D :=
  lt_of_lt_of_le (by positivity) (initialRadius_lower hν hK hD)

theorem duration_div_radius_sq {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    (hD : 1 ≤ D) (n : ℕ) :
    duration ν K D n / radius ν K D n ^ 2 =
      (16 * lambda D / initialRadius ν K D) *
        (K * D * (D / lambda D) ^ n + 2 * (lambda D)⁻¹ ^ n) := by
  have hr := ne_of_gt (initialRadius_pos hν hK hD)
  have hl := ne_of_gt (lambda_pos hD)
  unfold duration spacing radius count
  rw [pow_succ, pow_succ]
  simp only [div_pow, inv_pow]
  field_simp

private theorem coefficient_eq {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    (16 * lambda D / initialRadius ν K D) * (K * D + 2) =
      1 / (64 * 3000 * (1 + ν)) := by
  have hl := ne_of_gt (lambda_pos hD)
  have hν1 : 1 + ν ≠ 0 := by positivity
  have hkd : K * D + 2 ≠ 0 := by
    have : 0 ≤ K * D := mul_nonneg hK (by linarith)
    positivity
  unfold initialRadius
  field_simp
  ring

theorem loss_term_bound {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    0 ≤ duration ν K D n / radius ν K D n ^ 2 ∧
    duration ν K D n / radius ν K D n ^ 2 ≤
      (1 / (64 * 3000 * (1 + ν))) * (1 / 4 : ℝ) ^ n := by
  have hr := initialRadius_pos hν hK hD
  have hl := lambda_pos hD
  have hratio : D / lambda D = (1 / 4 : ℝ) := by
    dsimp [lambda]
    have : D ≠ 0 := by linarith
    field_simp
  have hinv : (lambda D)⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (lambda_ge_four hD)
  have hp : (lambda D)⁻¹ ^ n ≤ (1 / 4 : ℝ) ^ n :=
    pow_le_pow_left₀ (inv_nonneg.mpr hl.le) hinv n
  have hkd : 0 ≤ K * D := mul_nonneg hK (by linarith)
  rw [duration_div_radius_sq hν hK hD, hratio]
  constructor
  · positivity
  · calc
      (16 * lambda D / initialRadius ν K D) *
          (K * D * (1 / 4 : ℝ) ^ n + 2 * (lambda D)⁻¹ ^ n) ≤
          (16 * lambda D / initialRadius ν K D) *
            ((K * D + 2) * (1 / 4 : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = _ := by rw [← mul_assoc, coefficient_eq hν hK hD]

theorem summable_loss {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    Summable (fun n => duration ν K D n / radius ν K D n ^ 2) := by
  have hg : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_nonneg_of_le (fun n => (loss_term_bound hν hK hD n).1)
    (fun n => (loss_term_bound hν hK hD n).2) (hg.mul_left _)

theorem stages_loss_lt {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ν * 3000 * (∑' n : ℕ, duration ν K D n / radius ν K D n ^ 2) < (1 / 48 : ℝ) := by
  have hg : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hs : (∑' n : ℕ, duration ν K D n / radius ν K D n ^ 2) ≤
      (1 / (64 * 3000 * (1 + ν))) * (4 / 3 : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (64 * 3000 * (1 + ν))) * (1 / 4 : ℝ) ^ n :=
        Summable.tsum_le_tsum (fun n => (loss_term_bound hν hK hD n).2)
          (summable_loss hν hK hD) (hg.mul_left _)
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
          (by norm_num : (1 / 4 : ℝ) < 1)]
        norm_num
  calc
    _ ≤ ν * 3000 * ((1 / (64 * 3000 * (1 + ν))) * (4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (ν / (1 + ν)) / 48 := by field_simp; ring
    _ < 1 / 48 := by
      apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 48)
      exact (div_lt_one (by positivity)).mpr (by linarith)

theorem loading_loss_lt {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ν * 3000 / initialRadius ν K D ^ 2 < (1 / 48 : ℝ) := by
  have hr := initialRadius_pos hν hK hD
  have hlarge := initialRadius_lower hν hK hD
  have hνr : ν * 3000 < initialRadius ν K D := by linarith
  have h48 : (48 : ℝ) ≤ initialRadius ν K D := by linarith
  calc
    _ < initialRadius ν K D / initialRadius ν K D ^ 2 :=
      div_lt_div_of_pos_right hνr (sq_pos_of_pos hr)
    _ = 1 / initialRadius ν K D := by field_simp
    _ ≤ 1 / 48 := one_div_le_one_div_of_le (by norm_num) h48

theorem total_loss_lt {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ν * 3000 * ((initialRadius ν K D)⁻¹ ^ 2 +
      ∑' n : ℕ, duration ν K D n / radius ν K D n ^ 2) < (1 / 24 : ℝ) := by
  have hload := loading_loss_lt hν hK hD
  have hstages := stages_loss_lt hν hK hD
  rw [mul_add]
  have heq : ν * 3000 * (initialRadius ν K D)⁻¹ ^ 2 =
      ν * 3000 / initialRadius ν K D ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  rw [heq]
  linarith

theorem radius_ge_one {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    1 ≤ radius ν K D n := by
  have hr : 1 ≤ initialRadius ν K D := by
    have := initialRadius_lower hν hK hD
    linarith
  have hl : 1 ≤ lambda D := by linarith [lambda_ge_four hD]
  exact one_le_mul_of_one_le_of_one_le hr (one_le_pow₀ hl)

theorem radius_next_ge {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    2 * radius ν K D n ≤ radius ν K D (n + 1) := by
  have hr : 0 ≤ radius ν K D n := (radius_ge_one hν hK hD n).trans' (by norm_num)
  have hl : 2 ≤ lambda D := by linarith [lambda_ge_four hD]
  calc
    _ ≤ lambda D * radius ν K D n := mul_le_mul_of_nonneg_right hl hr
    _ = _ := by simp only [radius, pow_succ]; ring

theorem duration_ge_one {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    1 ≤ duration ν K D n := by
  have hc : 0 ≤ count K D (n + 1) := mul_nonneg hK (pow_nonneg (by linarith) _)
  have hr := radius_ge_one hν hK hD (n + 1)
  show 1 ≤ 16 * radius ν K D (n + 1) * (count K D (n + 1) + 2)
  nlinarith

theorem startTime_ge {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    (n : ℝ) + 1 ≤ startTime ν K D n := by
  induction n with
  | zero => simp [startTime]
  | succ n ih =>
    rw [startTime, Nat.cast_add, Nat.cast_one]
    linarith [duration_ge_one hν hK hD n]

theorem active_level_lt {ν K D T : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D)
    {Q n : ℕ} (hQ : T < (Q : ℝ)) (hn : startTime ν K D n ≤ T) : n < Q := by
  have h : (n : ℝ) < (Q : ℝ) := by linarith [startTime_ge hν hK hD n]
  exact_mod_cast h

theorem finitely_many_active_levels {ν K D T : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    (hD : 1 ≤ D) : {n : ℕ | startTime ν K D n ≤ T}.Finite := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt T
  exact (Set.finite_Iio Q).subset (fun n hn => active_level_lt hν hK hD hQ hn)

end VelocityDetection.Expanding
end

end OAI
