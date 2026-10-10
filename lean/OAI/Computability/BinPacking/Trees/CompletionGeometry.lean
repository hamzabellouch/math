import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace BinPackingGap.Geometry

abbrev Position (m R : ℕ) := Fin m × Fin R

def theta (R : ℕ) {m : ℕ} (e : Fin m) : ℚ :=
  ((R : ℚ) + 1) ^ e.val - 1

def heightCode (R : ℕ) {m : ℕ} (r : Position m R) : ℚ :=
  ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val - 1

def gap (m R : ℕ) : ℚ := 1 / (16 * ((R : ℚ) + 1) ^ m)

def baseline (m R : ℕ) (r : Position m R) : ℚ :=
  1 / 2 + gap m R * heightCode R r

def beta (m R : ℕ) (e : Fin m) : ℚ := gap m R * theta R e

def lambda (m R D ell : ℕ) : ℚ :=
  gap m R / (100 * ((D : ℚ) + 1)) ^ ell

def delta (m R D L : ℕ) : ℚ := lambda m R D L / 10

theorem base_pos (R : ℕ) : 0 < (R : ℚ) + 1 := by positivity

theorem base_one_le (R : ℕ) : 1 ≤ (R : ℚ) + 1 := by
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg R
  linarith

theorem widthScale_pos (D : ℕ) : 0 < 100 * ((D : ℚ) + 1) := by positivity

theorem widthScale_one_le (D : ℕ) : 1 ≤ 100 * ((D : ℚ) + 1) := by
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem gap_pos (m R : ℕ) : 0 < gap m R := by
  unfold gap
  positivity

theorem gap_nonneg (m R : ℕ) : 0 ≤ gap m R := (gap_pos m R).le

theorem gap_le_one_sixteen (m R : ℕ) : gap m R ≤ 1 / 16 := by
  unfold gap
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ m := one_le_pow₀ (base_one_le R)
  linarith

theorem gap_mul_power (m R : ℕ) : gap m R * ((R : ℚ) + 1) ^ m = 1 / 16 := by
  unfold gap
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 := (pow_pos (base_pos R) m).ne'
  field_simp [hp]

theorem theta_nonneg (R : ℕ) {m : ℕ} (e : Fin m) : 0 ≤ theta R e := by
  exact sub_nonneg.mpr (one_le_pow₀ (base_one_le R))

theorem theta_lt_power (R : ℕ) {m : ℕ} (e : Fin m) :
    theta R e < ((R : ℚ) + 1) ^ m := by
  have hp := pow_le_pow_right₀ (base_one_le R) (Nat.le_of_lt e.isLt)
  unfold theta
  linarith

theorem heightCode_nonneg (R : ℕ) {m : ℕ} (r : Position m R) :
    0 ≤ heightCode R r := by
  have hj : (1 : ℚ) ≤ (r.2.val : ℚ) + 1 := by
    have h := (Nat.cast_nonneg r.2.val : (0 : ℚ) ≤ r.2.val)
    linarith
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := one_le_pow₀ (base_one_le R)
  have hprod : (1 : ℚ) * 1 ≤ ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val :=
    mul_le_mul hj hp (by norm_num) (by positivity)
  unfold heightCode
  linarith

theorem heightCode_lt_power (R : ℕ) {m : ℕ} (r : Position m R) :
    heightCode R r < ((R : ℚ) + 1) ^ m := by
  have hj : (r.2.val : ℚ) + 1 < (R : ℚ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right r.2.isLt 1
  have hp : 0 < ((R : ℚ) + 1) ^ r.1.val := pow_pos (base_pos R) _
  have he : r.1.val + 1 ≤ m := r.1.isLt
  have hpow := pow_le_pow_right₀ (base_one_le R) he
  have hmul := mul_lt_mul_of_pos_right hj hp
  rw [pow_succ] at hpow
  unfold heightCode
  nlinarith

theorem baseline_lower (m R : ℕ) (r : Position m R) : 1 / 2 ≤ baseline m R r := by
  unfold baseline
  exact le_add_of_nonneg_right (mul_nonneg (gap_nonneg _ _) (heightCode_nonneg _ _))

theorem baseline_upper (m R : ℕ) (r : Position m R) : baseline m R r < 9 / 16 := by
  have h := mul_lt_mul_of_pos_left (heightCode_lt_power R r) (gap_pos m R)
  rw [gap_mul_power] at h
  unfold baseline
  linarith

theorem baseline_range (m R : ℕ) (r : Position m R) :
    1 / 2 ≤ baseline m R r ∧ baseline m R r < 9 / 16 :=
  ⟨baseline_lower _ _ _, baseline_upper _ _ _⟩

theorem beta_nonneg (m R : ℕ) (e : Fin m) : 0 ≤ beta m R e :=
  mul_nonneg (gap_nonneg _ _) (theta_nonneg _ _)

theorem beta_lt_one_sixteen (m R : ℕ) (e : Fin m) : beta m R e < 1 / 16 := by
  have h := mul_lt_mul_of_pos_left (theta_lt_power R e) (gap_pos m R)
  rwa [gap_mul_power] at h

theorem lambda_pos (m R D ell : ℕ) : 0 < lambda m R D ell :=
  div_pos (gap_pos _ _) (pow_pos (widthScale_pos D) ell)

theorem lambda_nonneg (m R D ell : ℕ) : 0 ≤ lambda m R D ell :=
  (lambda_pos _ _ _ _).le

@[simp] theorem lambda_zero (m R D : ℕ) : lambda m R D 0 = gap m R := by
  simp [lambda]

theorem lambda_succ (m R D ell : ℕ) :
    lambda m R D (ell + 1) = lambda m R D ell / (100 * ((D : ℚ) + 1)) := by
  simp only [lambda, pow_succ, div_div]

theorem lambda_antitone (m R D : ℕ) : Antitone (lambda m R D) := by
  intro a b hab
  exact div_le_div_of_nonneg_left (gap_nonneg m R) (pow_pos (widthScale_pos D) a)
    (pow_le_pow_right₀ (widthScale_one_le D) hab)

theorem lambda_le_gap (m R D ell : ℕ) : lambda m R D ell ≤ gap m R := by
  simpa only [lambda_zero] using lambda_antitone m R D (Nat.zero_le ell)

theorem lambda_le_one (m R D ell : ℕ) : lambda m R D ell ≤ 1 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

theorem lambda_lt_tenth (m R D ell : ℕ) : lambda m R D ell < 1 / 10 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

theorem lambda_one_le_hundredth (m R D : ℕ) : lambda m R D 1 ≤ gap m R / 100 := by
  unfold lambda
  rw [pow_one]
  apply div_le_div_of_nonneg_left (gap_nonneg _ _) (by norm_num)
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem delta_pos (m R D L : ℕ) : 0 < delta m R D L :=
  div_pos (lambda_pos _ _ _ _) (by norm_num)

theorem delta_nonneg (m R D L : ℕ) : 0 ≤ delta m R D L := (delta_pos _ _ _ _).le

theorem delta_le_tenth (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    delta m R D L ≤ lambda m R D ell / 10 :=
  div_le_div_of_nonneg_right (lambda_antitone m R D h) (by norm_num)

theorem delta_lt_gap (m R D L : ℕ) : delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D (Nat.zero_le L)
  rw [lambda_zero] at hd
  have hg := gap_pos m R
  linarith

theorem lambda_one_add_two_delta_lt_gap (m R D : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    lambda m R D 1 + 2 * delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D hL
  have hl := lambda_one_le_hundredth m R D
  have hg := gap_pos m R
  linarith

theorem children_succ_lt_parent (m R D ell : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D (ell + 1) < lambda m R D ell := by
  rw [lambda_succ, ← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 4 * (D : ℚ) + 1 < 100 * ((D : ℚ) + 1) := by
    have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
    linarith
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hcoeff (lambda_pos m R D ell)

theorem first_children_lt_gap_twentyfifth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < gap m R / 25 := by
  simp only [lambda, pow_one]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 25 * (4 * (D : ℚ) + 1) < 100 * ((D : ℚ) + 1) := by
    linarith
  have h := mul_lt_mul_of_pos_right hcoeff (gap_pos m R)
  nlinarith

theorem first_children_lt_tenth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < 1 / 10 := by
  have h := first_children_lt_gap_twentyfifth m R D
  have hg := gap_le_one_sixteen m R
  linarith

theorem lambda_add_delta_lt_three (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    lambda m R D ell + delta m R D L < 3 * lambda m R D ell := by
  have hd := delta_le_tenth m R D h
  have hl := lambda_pos m R D ell
  linarith

end BinPackingGap.Geometry

namespace BinPackingGap

def completion (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) : ℚ :=
  b - (if short then delta else 0) - globalLen - localLen

def completionInterval (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) :
    Set ℚ := Set.Ico (completion b short globalLen localLen delta) b

@[simp] theorem completion_false (b globalLen localLen delta : ℚ) :
    completion b false globalLen localLen delta = b - globalLen - localLen := by
  simp [completion]

@[simp] theorem completion_true (b globalLen localLen delta : ℚ) :
    completion b true globalLen localLen delta = b - delta - globalLen - localLen := by
  simp [completion]

theorem baseline_sub_completion (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) :
    b - completion b short globalLen localLen delta =
      (if short then delta else 0) + globalLen + localLen := by
  unfold completion
  ring

theorem completion_le_baseline (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short globalLen localLen delta ≤ b := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completion_length_nonneg (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    0 ≤ b - completion b short globalLen localLen delta :=
  sub_nonneg.mpr (completion_le_baseline b short globalLen localLen delta
    hglobal hlocal hdelta)

@[simp] theorem mem_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta a : ℚ) :
    a ∈ completionInterval b short globalLen localLen delta ↔
      completion b short globalLen localLen delta ≤ a ∧ a < b := Iff.rfl

theorem completion_le_deadline_iff (b : ℚ) (short : Bool)
    (globalLen localLen delta deadline : ℚ) :
    completion b short globalLen localLen delta ≤ deadline ↔
      b - (if short then delta else 0) - globalLen - localLen - deadline ≤ 0 := by
  unfold completion
  exact sub_nonpos.symm

theorem completion_zero_global_length_le (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hdelta : 0 ≤ delta) :
    b - completion b short 0 localLen delta ≤ localLen + delta := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completion_zero_global_interval_subset (b : ℚ) (short : Bool)
    (localLen delta : ℚ) (hdelta : 0 ≤ delta) :
    completionInterval b short 0 localLen delta ⊆ Set.Ico (b - (localLen + delta)) b := by
  intro a ha
  have hlength := completion_zero_global_length_le b short localLen delta hdelta
  exact ⟨by linarith [ha.1], ha.2⟩

theorem completion_zero_global_bounds (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short 0 localLen delta ∈ Set.Icc (b - (localLen + delta)) b := by
  constructor
  · linarith [completion_zero_global_length_le b short localLen delta hdelta]
  · exact completion_le_baseline b short 0 localLen delta le_rfl hlocal hdelta

@[simp] theorem completion_long_zero_lengths (b delta : ℚ) :
    completion b false 0 0 delta = b := by simp

@[simp] theorem completion_short_zero_lengths (b delta : ℚ) :
    completion b true 0 0 delta = b - delta := by simp

@[simp] theorem completionInterval_long_zero_lengths (b delta : ℚ) :
    completionInterval b false 0 0 delta = ∅ := by
  simp [completionInterval]

theorem completionInterval_short_zero_lengths (b delta : ℚ) :
    completionInterval b true 0 0 delta = Set.Ico (b - delta) b := by
  simp [completionInterval]

theorem completion_plus_le_one (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hbaseline : b ≤ 1) (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen)
    (hdelta : 0 ≤ delta) : completion b short globalLen localLen delta ≤ 1 :=
  (completion_le_baseline b short globalLen localLen delta hglobal hlocal hdelta).trans
    hbaseline

theorem completion_minus_gt_one (b : ℚ) (short : Bool) (globalLen localLen delta lambdaOne : ℚ)
    (hbaseline : 4 ≤ b) (hshort : short = false) (hglobal : globalLen ≤ 1)
    (hlocal : localLen ≤ lambdaOne) (hlambda : lambdaOne < 1) :
    1 < completion b short globalLen localLen delta := by
  subst short
  rw [completion_false]
  linarith

theorem not_mem_plus_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta a : ℚ) (hbaseline : b ≤ 1) (ha : 1 ≤ a) :
    a ∉ completionInterval b short globalLen localLen delta := by
  intro hmem
  linarith [hmem.2]

theorem not_mem_minus_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta lambdaOne a : ℚ) (hbaseline : 4 ≤ b)
    (hshort : short = false) (hglobal : globalLen ≤ 1)
    (hlocal : localLen ≤ lambdaOne) (hlambda : lambdaOne < 1) (ha : a ≤ 1) :
    a ∉ completionInterval b short globalLen localLen delta := by
  intro hmem
  have hh := completion_minus_gt_one b short globalLen localLen delta lambdaOne
    hbaseline hshort hglobal hlocal hlambda
  linarith [hmem.1]

theorem completion_zero_global_geometry_length_le (m R D L ell : ℕ)
    (b : ℚ) (short : Bool) :
    b - completion b short 0 (Geometry.lambda m R D ell) (Geometry.delta m R D L) ≤
      Geometry.lambda m R D ell + Geometry.delta m R D L :=
  completion_zero_global_length_le b short _ _ (Geometry.delta_nonneg m R D L)

theorem completion_minus_geometry_gt_one (m R D L : ℕ) (b : ℚ) (short : Bool)
    (globalLen localLen : ℚ) (hbaseline : 4 ≤ b) (hshort : short = false)
    (hglobal : globalLen ≤ 1) (hlocal : localLen ≤ Geometry.lambda m R D 1) :
    1 < completion b short globalLen localLen (Geometry.delta m R D L) := by
  apply completion_minus_gt_one b short globalLen localLen _ (Geometry.lambda m R D 1)
    hbaseline hshort hglobal hlocal
  linarith [Geometry.lambda_lt_tenth m R D 1]

theorem completion_job_interval (m R D L : ℕ) (r : Geometry.Position m R) :
    completionInterval (Geometry.baseline m R r) true 0 0 (Geometry.delta m R D L) =
      Set.Ico (Geometry.baseline m R r - Geometry.delta m R D L)
        (Geometry.baseline m R r) :=
  completionInterval_short_zero_lengths _ _

end BinPackingGap

end OAI
