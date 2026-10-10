import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityTriangle

namespace OAI

/-! Radial coordinates and angular representatives for the interior density construction. -/
noncomputable section
open Set

namespace ClosedSurfaceR4.LoopDensity

lemma radial_representation {c : Plane} (hc : c 0 ^ 2 + c 1 ^ 2 < 1) :
    ∃ (r : ℝ) (e : Plane), 0 ≤ r ∧ r < 1 ∧ e 0 ^ 2 + e 1 ^ 2 = 1 ∧ c = r • e := by
  let r := Real.sqrt (c 0 ^ 2 + c 1 ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = c 0 ^ 2 + c 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hr1 : r < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by positivity) hc
  by_cases hz : r = 0
  · have hc0 : c 0 = 0 := by nlinarith
    have hc1 : c 1 = 0 := by nlinarith
    refine ⟨0, ![1, 0], le_rfl, zero_lt_one, by norm_num, ?_⟩
    ext i
    fin_cases i <;> simp [hc0, hc1]
  · let e : Plane := fun i => c i / r
    refine ⟨r, e, hr, hr1, ?_, ?_⟩
    · change (c 0 / r) ^ 2 + (c 1 / r) ^ 2 = 1
      field_simp
      nlinarith [hr2]
    · ext i
      change c i = r * (c i / r)
      field_simp

lemma unit_direction_angle {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    ∃ β ∈ Icc (-Real.pi) Real.pi, Real.cos β = e 0 ∧ Real.sin β = e 1 := by
  let z : ℂ := ⟨e 0, e 1⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    change Real.sqrt (e 0 ^ 2 + e 1 ^ 2) = 1
    rw [he, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  refine ⟨Complex.arg z, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hz, hn, div_one]
  · rw [Complex.sin_arg, hn, div_one]

end ClosedSurfaceR4.LoopDensity

end

end OAI
