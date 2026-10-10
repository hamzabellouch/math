import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupObservation

namespace OAI

/-! # The exact rescaled pointwise limit in physical time -/

open Filter Topology

namespace DefocusingNLS

theorem expanding_clock_denominator_pos_of_lt (L t : ℝ) (hL : 0 < L)
    (ht : t < L ^ (-2 : ℝ)) : 0 < 1 - L ^ 2 * t := by
  have hT : 0 < L ^ (-2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hc : L ^ (-2 : ℝ) * L ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hL]
    norm_num
  have he : L ^ (-2 : ℝ) - t = L ^ (-2 : ℝ) * (1 - L ^ 2 * t) := by
    calc
      _ = L ^ (-2 : ℝ) - (L ^ (-2 : ℝ) * L ^ 2) * t := by rw [hc, one_mul]
      _ = _ := by ring
  have hp : 0 < L ^ (-2 : ℝ) - t := sub_pos.mpr ht
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left hT).mp hp

theorem expandingInverseClock_nonneg (L t : ℝ) (hL : 0 < L)
    (ht : t ∈ Set.Ico 0 (L ^ (-2 : ℝ))) : 0 ≤ expandingInverseClock L t := by
  unfold expandingInverseClock
  apply neg_nonneg.mpr
  exact Real.log_nonpos (expanding_clock_denominator_pos_of_lt L t hL ht.2).le
    (by nlinarith [mul_nonneg (sq_nonneg L) ht.1])

theorem expandingInverseClock_eq_similarityTime (L t : ℝ) (hL : 0 < L)
    (ht : t < L ^ (-2 : ℝ)) :
    expandingInverseClock L t = similarityTime (L ^ (-2 : ℝ)) t := by
  have hT : 0 < L ^ (-2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hc : L ^ (-2 : ℝ) * L ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hL]
    norm_num
  have he : L ^ (-2 : ℝ) - t = L ^ (-2 : ℝ) * (1 - L ^ 2 * t) := by
    calc
      _ = L ^ (-2 : ℝ) - (L ^ (-2 : ℝ) * L ^ 2) * t := by rw [hc, one_mul]
      _ = _ := by ring
  have hb : 0 < 1 - L ^ 2 * t :=
    (mul_pos_iff_of_pos_left hT).mp (he ▸ sub_pos.mpr ht)
  have hratio : L ^ (-2 : ℝ) / (L ^ (-2 : ℝ) - t) = (1 - L ^ 2 * t)⁻¹ := by
    rw [he]
    field_simp [hT.ne', hb.ne']
  rw [expandingInverseClock, similarityTime, hratio, Real.log_inv]

theorem expandingInverseClock_tendsto (L : ℝ) (hL : 0 < L) :
    Tendsto (expandingInverseClock L) (𝓝[<] (L ^ (-2 : ℝ))) atTop := by
  apply (similarityTime_tendsto (L ^ (-2 : ℝ)) (Real.rpow_pos_of_pos hL _)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (expandingInverseClock_eq_similarityTime L t hL ht).symm

theorem expanding_rescaled_amplitude (a b L s : ℝ) (hL : 0 < L) :
    (L ^ (-2 : ℝ) - expandingFreeTime L s) ^ a *
      ‖expandingPhysicalAmplitude a b L s‖ = 1 := by
  have he : L ^ (-2 : ℝ) - expandingFreeTime L s = L ^ (-2 : ℝ) * Real.exp (-s) := by
    unfold expandingFreeTime
    ring
  have hp : (L ^ (-2 : ℝ)) ^ a * L ^ (2 * a) = 1 := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    rw [show (-2 : ℝ) * a + 2 * a = 0 by ring, Real.rpow_zero]
  rw [he, expandingPhysicalAmplitude_norm a b L s hL,
    Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.exp_pos _).le, ← Real.exp_mul]
  calc
    _ = ((L ^ (-2 : ℝ)) ^ a * L ^ (2 * a)) *
        (Real.exp (-s * a) * Real.exp (a * s)) := by ring
    _ = 1 := by
      rw [hp, ← Real.exp_add, show -s * a + a * s = 0 by ring, Real.exp_zero, one_mul]

theorem expanding_rescaled_observation (a b L t : ℝ) (hL : 0 < L)
    (ht : t < L ^ (-2 : ℝ)) (z : ℂ) :
    (L ^ (-2 : ℝ) - t) ^ a *
      ‖expandingPhysicalAmplitude a b L (expandingInverseClock L t) * z‖ = ‖z‖ := by
  have hd := expanding_clock_denominator_pos_of_lt L t hL ht
  have h := expanding_rescaled_amplitude a b L (expandingInverseClock L t) hL
  rw [expandingFreeTime_inverseClock L t hL hd] at h
  rw [norm_mul, ← mul_assoc, h, one_mul]

/-- The rescaled modulus limit required in the main theorem follows from
the similarity observation limit. -/
theorem expanding_rescaled_observation_limit (a b L : ℝ) (hL : 0 < L)
    (g : ℝ → ℂ) (c : ℂ) (hg : Tendsto g atTop (𝓝 c)) :
    Tendsto (fun t => (L ^ (-2 : ℝ) - t) ^ a *
      ‖expandingPhysicalAmplitude a b L (expandingInverseClock L t) *
        g (expandingInverseClock L t)‖)
      (𝓝[<] (L ^ (-2 : ℝ))) (𝓝 ‖c‖) := by
  have h := (hg.comp (expandingInverseClock_tendsto L hL)).norm
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (expanding_rescaled_observation a b L t hL ht _).symm

end DefocusingNLS

end OAI
