import Mathlib

namespace OAI

noncomputable section

namespace Problem340.Clock

def profileCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 36 / 25
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℝ := profileCutoff (x ^ 2)

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := profileCutoff.nonneg

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := profileCutoff.le_one

lemma cutoff_neg (x : ℝ) : cutoff (-x) = cutoff x := by simp [cutoff]

lemma contDiff_cutoff {n : ℕ∞} : ContDiff ℝ n cutoff :=
  profileCutoff.contDiff.comp (contDiff_id.pow 2)

def profile (s : ℝ) : ℝ := profileCutoff s * s / 4 + 1 - profileCutoff s

lemma contDiff_profile {n : ℕ∞} : ContDiff ℝ n profile := by
  unfold profile
  exact (((profileCutoff.contDiff.mul contDiff_id).div_const 4).add contDiff_const).sub
    profileCutoff.contDiff

def localBarrier (x : ℝ) : ℝ := cutoff x * x ^ 2 / 4 + 1 - cutoff x

lemma localBarrier_eq_profile (x : ℝ) : localBarrier x = profile (x ^ 2) := rfl

lemma cutoff_one {x : ℝ} (hx : |x| ≤ 1) : cutoff x = 1 := by
  apply profileCutoff.one_of_mem_closedBall
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  simpa [profileCutoff, Real.dist_eq, abs_of_nonneg (sq_nonneg x)] using hx2

lemma cutoff_zero {x : ℝ} (hx : 6 / 5 ≤ |x|) : cutoff x = 0 := by
  apply profileCutoff.zero_of_le_dist
  have hx2 : 36 / 25 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  simpa [profileCutoff, Real.dist_eq, abs_of_nonneg (sq_nonneg x)] using hx2

lemma localBarrier_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    localBarrier x = x ^ 2 / 4 := by
  simp [localBarrier, cutoff_one hx]

lemma localBarrier_of_abs_ge {x : ℝ} (hx : 6 / 5 ≤ |x|) :
    localBarrier x = 1 := by
  simp [localBarrier, cutoff_zero hx]

lemma localBarrier_nonneg (x : ℝ) : 0 ≤ localBarrier x := by
  have hη : 0 ≤ cutoff x := cutoff_nonneg _
  have hη' : cutoff x ≤ 1 := cutoff_le_one _
  have hp : 0 ≤ cutoff x * x ^ 2 / 4 := by positivity
  unfold localBarrier
  linarith

lemma localBarrier_le_one (x : ℝ) : localBarrier x ≤ 1 := by
  by_cases hx : 6 / 5 ≤ |x|
  · rw [localBarrier_of_abs_ge hx]
  · have hx' : |x| < 6 / 5 := lt_of_not_ge hx
    have hx2 : x ^ 2 ≤ 4 := by
      have hm := (abs_lt.mp hx').1
      have hp := (abs_lt.mp hx').2
      nlinarith [sq_nonneg x]
    have hη : 0 ≤ cutoff x := cutoff_nonneg _
    have hmul : cutoff x * x ^ 2 ≤ cutoff x * 4 := mul_le_mul_of_nonneg_left hx2 hη
    unfold localBarrier
    linarith

lemma localBarrier_eq_zero_iff (x : ℝ) : localBarrier x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hη : 0 ≤ cutoff x := cutoff_nonneg _
    have hη' : cutoff x ≤ 1 := cutoff_le_one _
    have hp : 0 ≤ cutoff x * x ^ 2 / 4 := by positivity
    have h1 : cutoff x = 1 := by
      unfold localBarrier at hx
      linarith
    unfold localBarrier at hx
    rw [h1] at hx
    nlinarith [sq_nonneg x]
  · rintro rfl
    norm_num [localBarrier, cutoff_one (x := 0) (by norm_num)]

lemma localBarrier_neg (x : ℝ) : localBarrier (-x) = localBarrier x := by
  simp [localBarrier, cutoff_neg]

lemma contDiff_localBarrier {n : ℕ∞} : ContDiff ℝ n localBarrier := by
  unfold localBarrier
  exact (((contDiff_cutoff.mul (contDiff_id.pow 2)).div_const 4).add contDiff_const).sub
    contDiff_cutoff

lemma profile_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ profile s := by
  have h := localBarrier_nonneg (Real.sqrt s)
  rwa [localBarrier_eq_profile, Real.sq_sqrt hs] at h

lemma profile_le_one {s : ℝ} (hs : 0 ≤ s) : profile s ≤ 1 := by
  have h := localBarrier_le_one (Real.sqrt s)
  rwa [localBarrier_eq_profile, Real.sq_sqrt hs] at h

lemma profile_eq_zero_iff {s : ℝ} (hs : 0 ≤ s) : profile s = 0 ↔ s = 0 := by
  have h := localBarrier_eq_zero_iff (Real.sqrt s)
  rw [localBarrier_eq_profile, Real.sq_sqrt hs, Real.sqrt_eq_zero hs] at h
  exact h

def coordinate (t : ℝ) : ℝ := 30 * Real.sin (Real.pi * (t - 50) / 100)

lemma contDiff_coordinate {n : ℕ∞} : ContDiff ℝ n coordinate := by
  unfold coordinate
  fun_prop

lemma coordinate_add_period (t : ℝ) : coordinate (t + 100) = -coordinate t := by
  unfold coordinate
  have heq : Real.pi * (t + 100 - 50) / 100 =
      Real.pi * (t - 50) / 100 + Real.pi := by ring
  rw [heq, Real.sin_add_pi]
  ring

lemma abs_coordinate_le (t : ℝ) : |coordinate t| ≤ |t - 50| := by
  have hs : |Real.sin (Real.pi * (t - 50) / 100)| ≤
      |Real.pi * (t - 50) / 100| := Real.abs_sin_le_abs
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  have hπ : 30 * Real.pi ≤ 100 := by linarith [Real.pi_lt_d2]
  have ha : 0 ≤ |t - 50| := abs_nonneg _
  simp only [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos (show (0 : ℝ) < 100 by norm_num)] at hs
  unfold coordinate
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 30 by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_right hπ ha]

def barrier (t : ℝ) : ℝ := localBarrier (coordinate t)

lemma contDiff_barrier {n : ℕ∞} : ContDiff ℝ n barrier :=
  contDiff_localBarrier.comp contDiff_coordinate

lemma barrier_periodic : Function.Periodic barrier 100 := by
  intro t
  simp only [barrier, coordinate_add_period, localBarrier_neg]

lemma barrier_nonneg (t : ℝ) : 0 ≤ barrier t := localBarrier_nonneg _

lemma barrier_le_one (t : ℝ) : barrier t ≤ 1 := localBarrier_le_one _

lemma barrier_stops (t : ℝ) (ht : t ≤ 50) : t + barrier t ≤ 50 := by
  by_cases hsmall : 50 - t ≤ 1
  · have hd : 0 ≤ 50 - t := by linarith
    have habs : |t - 50| = 50 - t := by rw [abs_of_nonpos (by linarith)]; ring
    have hcoord : |coordinate t| ≤ 1 := by
      calc |coordinate t| ≤ |t - 50| := abs_coordinate_le t
           _ ≤ 1 := by rw [habs]; exact hsmall
    have hbound : (coordinate t) ^ 2 ≤ (50 - t) ^ 2 := by
      have h := abs_coordinate_le t
      rw [habs] at h
      nlinarith [(abs_nonneg (coordinate t)), sq_abs (coordinate t)]
    rw [barrier, localBarrier_of_abs_le_one hcoord]
    nlinarith
  · have hlarge : 1 ≤ 50 - t := le_of_lt (lt_of_not_ge hsmall)
    linarith [barrier_le_one t]

lemma barrier_eq_zero_iff (t : ℝ) :
    barrier t = 0 ↔ ∃ k : ℤ, t = 50 + 100 * (k : ℝ) := by
  rw [barrier, localBarrier_eq_zero_iff]
  unfold coordinate
  rw [mul_eq_zero]
  simp only [show (30 : ℝ) ≠ 0 by norm_num, false_or, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    apply (mul_right_inj' hp).mp
    nlinarith [hk]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    ring

lemma abs_coordinate_lower {t : ℝ} (ht : |t - 50| ≤ 50) :
    (3 / 5 : ℝ) * |t - 50| ≤ |coordinate t| := by
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  have ha : |Real.pi * (t - 50) / 100| = Real.pi * |t - 50| / 100 := by
    rw [abs_div, abs_mul, abs_of_nonneg hp]
    norm_num
  have harg : |Real.pi * (t - 50) / 100| ≤ Real.pi / 2 := by
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left ht hp]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [ha] at hs
  have heq : 2 / Real.pi * (Real.pi * |t - 50| / 100) = |t - 50| / 50 := by
    field_simp
    ring
  rw [heq] at hs
  unfold coordinate
  rw [abs_mul]
  norm_num
  linarith

lemma barrier_plateau {t : ℝ} (ht0 : 0 ≤ t) (ht100 : t ≤ 100)
    (hfar : 2 ≤ |t - 50|) : barrier t = 1 := by
  apply localBarrier_of_abs_ge
  have habs : |t - 50| ≤ 50 := by
    apply abs_le.mpr
    constructor <;> linarith
  have h := abs_coordinate_lower habs
  linarith

lemma coordinate_sq (t : ℝ) :
    coordinate t ^ 2 = 450 * (1 + Real.cos (2 * Real.pi * t / 100)) := by
  have hangle : Real.pi * (t - 50) / 100 = Real.pi * t / 100 - Real.pi / 2 := by ring
  have hcos := Real.cos_two_mul (Real.pi * t / 100)
  have hdouble : 2 * (Real.pi * t / 100) = 2 * Real.pi * t / 100 := by ring
  rw [hdouble] at hcos
  unfold coordinate
  rw [hangle, Real.sin_sub_pi_div_two]
  nlinarith

def ambientBarrier (x : EuclideanSpace ℝ (Fin 2)) : ℝ := profile (450 * (1 + x 0))

lemma contDiff_ambientBarrier {n : ℕ∞} : ContDiff ℝ n ambientBarrier := by
  apply contDiff_profile.comp
  exact contDiff_const.mul (contDiff_const.add (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff)

lemma ambientBarrier_on_circle (t : ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hx : x 0 = Real.cos (2 * Real.pi * t / 100)) :
    ambientBarrier x = barrier t := by
  rw [ambientBarrier, hx, barrier, localBarrier_eq_profile, coordinate_sq]

lemma ambientBarrier_mem_Icc (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ ≤ 1) :
    ambientBarrier x ∈ Set.Icc (0 : ℝ) 1 := by
  have habs : |x 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x (0 : Fin 2)).trans hx
  have hfirst : -1 ≤ x 0 := (abs_le.mp habs).1
  have hs : 0 ≤ 450 * (1 + x 0) := by linarith
  exact ⟨profile_nonneg hs, profile_le_one hs⟩

lemma ambientBarrier_eq_zero_iff (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ ≤ 1) :
    ambientBarrier x = 0 ↔ x 0 = -1 := by
  have habs : |x 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x (0 : Fin 2)).trans hx
  have hfirst : -1 ≤ x 0 := (abs_le.mp habs).1
  have hs : 0 ≤ 450 * (1 + x 0) := by linarith
  rw [ambientBarrier, profile_eq_zero_iff hs]
  constructor <;> intro h <;> linarith

def increment (t e : ℝ) : ℝ := barrier t + (1 - barrier t) * e

lemma increment_nonneg (t : ℝ) {e : ℝ} (he : 0 ≤ e) :
    0 ≤ increment t e := by
  unfold increment
  have hb := barrier_nonneg t
  have hb' := barrier_le_one t
  positivity

lemma barrier_le_increment (t : ℝ) {e : ℝ} (he : 0 ≤ e) :
    barrier t ≤ increment t e := by
  unfold increment
  have hp : 0 ≤ (1 - barrier t) * e := mul_nonneg (sub_nonneg.mpr (barrier_le_one t)) he
  linarith

lemma increment_le_one (t : ℝ) {e : ℝ} (he : e ≤ 1) : increment t e ≤ 1 := by
  unfold increment
  have hp := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr (barrier_le_one t))
  linarith

@[simp] lemma increment_zero (t : ℝ) : increment t 0 = barrier t := by
  simp [increment]

@[simp] lemma increment_one (t : ℝ) : increment t 1 = 1 := by
  simp [increment]

lemma increment_eq_one_of_barrier_eq_one {t e : ℝ} (h : barrier t = 1) :
    increment t e = 1 := by
  simp [increment, h]

lemma increment_periodic (e : ℝ) : Function.Periodic (fun t => increment t e) 100 := by
  intro t
  simp only [increment, barrier_periodic t]

lemma contDiff_increment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {t e : E → ℝ} (ht : ContDiff ℝ n t) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun x => increment (t x) (e x)) := by
  exact (contDiff_barrier.comp ht).add
    ((contDiff_const.sub (contDiff_barrier.comp ht)).mul he)

end Problem340.Clock

end

end OAI
