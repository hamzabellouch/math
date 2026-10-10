import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusL2Product

namespace OAI

/-! # Physical-volume normalization of the continuous torus L² realization -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance torusPhysicalL2Measure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusPhysicalL2Probability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuousTorusL2_norm_sq (f : C(T, ℂ)) :
    ‖f.toLp 2 volume ℂ‖ ^ 2 = ∫ x : T, ‖f x‖ ^ 2 := by
  have he := real_inner_self_eq_norm_sq (f.toLp 2 volume ℂ)
  rw [L2.inner_def] at he
  rw [← he]
  apply integral_congr_ae
  have hf : (f.toLp 2 volume ℂ : Lp ℂ 2 (volume : Measure T)) =ᵐ[volume] f :=
    ContinuousMap.coeFn_toLp volume f
  filter_upwards [hf] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

noncomputable def torusPhysicalL2Value (L : ℝ) (f : C(T, ℂ)) : Lp ℂ 2 (volume : Measure T) :=
  ((2 * Real.pi * L) ^ 6 : ℝ) • f.toLp 2 volume ℂ

theorem torusPhysicalL2Value_norm_sq (L : ℝ) (f : C(T, ℂ)) :
    ‖torusPhysicalL2Value L f‖ ^ 2 =
      (2 * Real.pi * L) ^ 12 * (∫ x : T, ‖f x‖ ^ 2) := by
  rw [torusPhysicalL2Value, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    continuousTorusL2_norm_sq, ← pow_mul]

end DefocusingNLS

end OAI
