import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityDirections

namespace OAI

/-! The interior oscillatory path covers the whole velocity circle. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

def interiorPath (A h t : ℝ) : Plane :=
  ![Real.cos (h + A * Real.cos (2 * Real.pi * t)),
    Real.sin (h + A * Real.cos (2 * Real.pi * t))]

lemma interiorPath_continuous (A h : ℝ) : Continuous (interiorPath A h) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t => Real.cos (h + A * Real.cos (2 * Real.pi * t)))
    fun_prop
  · change Continuous (fun t => Real.sin (h + A * Real.cos (2 * Real.pi * t)))
    fun_prop

/-- All circle directions occur away from the endpoints and turning points. -/
theorem interiorPath_covers {A h : ℝ} (hA : Real.pi + |h| < A)
    {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, interiorPath A h t = e := by
  obtain ⟨β, hβ, hcos, hsin⟩ := unit_direction_angle he
  have hAp : 0 < A := lt_of_lt_of_le Real.pi_pos (by linarith [abs_nonneg h])
  have hlo : -1 < (β - h) / A := (lt_div_iff₀ hAp).mpr (by linarith [le_abs_self h, hβ.1])
  have hhi : (β - h) / A < 1 := (div_lt_iff₀ hAp).mpr (by linarith [neg_abs_le h, hβ.2])
  let x := Real.arccos ((β - h) / A)
  have hx0 : 0 < x := Real.arccos_pos.mpr hhi
  have hxπ : x < Real.pi := Real.arccos_lt_pi.mpr hlo
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨x / (2 * Real.pi), ⟨div_pos hx0 hp, (div_lt_one hp).mpr (by linarith [Real.pi_pos])⟩, ?_⟩
  have hcancel : 2 * Real.pi * (x / (2 * Real.pi)) = x := by field_simp
  have hcx : Real.cos x = (β - h) / A := Real.cos_arccos hlo.le hhi.le
  have harg : h + A * ((β - h) / A) = β := by field_simp; ring
  ext i
  fin_cases i <;> simp [interiorPath, hcancel, hcx, harg, hcos, hsin]

end ClosedSurfaceR4.LoopDensity

end

end OAI
