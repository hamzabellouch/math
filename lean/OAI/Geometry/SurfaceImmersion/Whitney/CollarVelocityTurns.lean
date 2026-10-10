import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityAngle

namespace OAI

/-! Exact turning positions for the collar arc, including after reparametrization. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

lemma clock_of_sin_eq_zero (a : ℝ) {t : ℝ} (ht : Real.sin t = 0) : clock a t = t := by
  simp [clock, Real.sin_two_mul, ht]

lemma inverseClock_of_sin_eq_zero (a : ℝ) {t : ℝ} (ht : Real.sin t = 0) :
    inverseClock a t = t := by
  apply (clock_strictMono a).injective
  rw [clock_inverseClock, clock_of_sin_eq_zero a ht]

lemma sin_inverseClock_eq_zero_iff (a θ : ℝ) :
    Real.sin (inverseClock a θ) = 0 ↔ Real.sin θ = 0 := by
  constructor
  · intro h
    have ht := clock_of_sin_eq_zero a h
    rw [clock_inverseClock] at ht
    rwa [ht]
  · intro h
    rwa [inverseClock_of_sin_eq_zero a h]

lemma deriv_angle_eq_zero_iff_sin {a θ : ℝ} (ha : a ≠ 0) :
    deriv (angle a) θ = 0 ↔ Real.sin θ = 0 :=
  (deriv_angle_eq_zero_iff ha).trans (sin_inverseClock_eq_zero_iff a θ)

/-- There are precisely two turns in one half-open period. -/
theorem angle_two_turns {a θ : ℝ} (ha : a ≠ 0) (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    deriv (angle a) θ = 0 ↔ θ = 0 ∨ θ = Real.pi := by
  rw [deriv_angle_eq_zero_iff_sin ha]
  constructor
  · intro h
    by_cases hp : θ < Real.pi
    · left
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos, hθ.1]) hp).mp h
    · right
      have hs : Real.sin (θ - Real.pi) = 0 := by
        simp [Real.sin_sub, h]
      have hz := (Real.sin_eq_zero_iff_of_lt_of_lt
        (x := θ - Real.pi) (by linarith [Real.pi_pos]) (by linarith [hθ.2])).mp hs
      linarith
  · rintro (rfl | rfl) <;> simp

@[simp] lemma angle_zero (a : ℝ) : angle a 0 = 2 * Real.arctan a := by
  simp [angle, baseAngle]

lemma angle_pi (a : ℝ) : angle a Real.pi = -2 * Real.arctan a := by
  rw [angle, inverseClock_of_sin_eq_zero a Real.sin_pi]
  simp [baseAngle, Real.arctan_neg]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
