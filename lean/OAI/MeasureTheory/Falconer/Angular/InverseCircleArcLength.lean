import OAI.MeasureTheory.Falconer.Angular.RotatedInverseCircle
import OAI.MeasureTheory.Falconer.Angular.StationaryArcLength

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem periodic_sourceAngle_complex {f : ℝ → ℂ}
    (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm, add_comm] using hp θ

noncomputable def inverseCircleOperator (j : ℕ) (b : UnitCircle → ℂ) : UnitCircle → ℂ :=
  fun dir => inverseStationaryOperator j (fun θ => b (sourceUnitDirection θ)) (sourceAngle dir)

theorem inverseCircleOperator_comp (j : ℕ) (b : UnitCircle → ℂ) (θ : ℝ) :
    inverseCircleOperator j b (sourceUnitDirection θ) =
      inverseStationaryOperator j (fun φ => b (sourceUnitDirection φ)) θ := by
  have hp : Function.Periodic (fun φ => b (sourceUnitDirection φ)) (2*Real.pi) :=
    fun φ => congrArg b (sourceUnitDirection_periodic φ)
  exact periodic_sourceAngle_complex ((inverseStationaryExpr j).apply_periodic hp) θ

theorem circle_measurable_of_angular {b : UnitCircle → ℂ}
    (hb : Continuous (fun θ => b (sourceUnitDirection θ))) : Measurable b := by
  have he : b = (fun θ => b (sourceUnitDirection θ)) ∘ sourceAngle := by
    funext dir
    simp [sourceUnitDirection_sourceAngle]
  rw [he]
  exact hb.measurable.comp measurable_sourceAngle

theorem inverseCircleOperator_measurable (j : ℕ) {b : UnitCircle → ℂ}
    (hb : ContDiff ℝ ∞ (fun θ => b (sourceUnitDirection θ))) :
    Measurable (inverseCircleOperator j b) :=
  (inverseStationaryOperator_contDiff j hb).continuous.measurable.comp measurable_sourceAngle

theorem inner_sourceDirection (θ φ : ℝ) :
    inner ℝ (sourceDirection θ) (sourceDirection φ) = Real.cos (θ-φ) := by
  unfold sourceDirection
  rw [LinearIsometryEquiv.inner_map_map]
  simp [Complex.inner, Real.cos_sub, -Complex.ofReal_cos, -Complex.ofReal_sin, mul_comm]

theorem displacement_has_angle {Δ : Plane} (hΔ : Δ ≠ 0) :
    ∃ θ₀ : ℝ, Δ = ‖Δ‖ • sourceDirection θ₀ := by
  have hp : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ
  let e : UnitCircle := ⟨‖Δ‖⁻¹ • Δ, by
    simp [norm_smul, hp.ne']⟩
  refine ⟨sourceAngle e, ?_⟩
  have he := congrArg (fun dir : UnitCircle => (dir:Plane)) (sourceUnitDirection_sourceAngle e)
  change sourceDirection (sourceAngle e) = ‖Δ‖⁻¹ • Δ at he
  rw [he, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

noncomputable def sourceInverseCircleIntegral (n : ℕ) (r : ℝ) (Δ : Plane)
    (ψ b : UnitCircle → ℂ) : ℂ :=
  (((r*‖Δ‖)^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), (((r*‖Δ‖)⁻¹:ℝ):ℂ)^j *
    ∫ dir, Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (dir:Plane) Δ:ℂ)) *
      (ψ dir * inverseCircleOperator j b dir) ∂sourceArcLength

theorem sourceInverseCircleIntegral_eq (n : ℕ) (r θ₀ : ℝ) {Δ : Plane}
    (hΔ : Δ = ‖Δ‖ • sourceDirection θ₀) {ψ b : UnitCircle → ℂ}
    (hψ : Continuous (fun θ => ψ (sourceUnitDirection θ)))
    (hb : ContDiff ℝ ∞ (fun θ => b (sourceUnitDirection θ))) :
    sourceInverseCircleIntegral n r Δ ψ b =
      rotatedInverseCircleIntegral n (r*‖Δ‖) θ₀
        (fun θ => ψ (sourceUnitDirection θ)) (fun θ => b (sourceUnitDirection θ)) := by
  unfold sourceInverseCircleIntegral rotatedInverseCircleIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hmeas : Measurable (fun dir : UnitCircle =>
      Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (dir:Plane) Δ:ℂ)) *
        (ψ dir * inverseCircleOperator j b dir)) := by
    apply Measurable.mul
    · fun_prop
    · exact (circle_measurable_of_angular hψ).mul (inverseCircleOperator_measurable j hb)
  rw [sourceArcLength_integral_period hmeas.aestronglyMeasurable]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [inverseCircleOperator_comp]
  congr 1
  have he : inner ℝ (sourceDirection θ) Δ = ‖Δ‖*Real.cos (θ-θ₀) := by
    calc
      _ = inner ℝ (sourceDirection θ) (‖Δ‖ • sourceDirection θ₀) :=
        congrArg (inner ℝ (sourceDirection θ)) hΔ
      _ = _ := by rw [inner_smul_right, inner_sourceDirection]
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection θ) Δ:ℂ)) = _
  rw [he]
  simp only [cosineOscillator, Complex.ofReal_mul]
  congr 1
  ring

end PlanarFalconer

end OAI
