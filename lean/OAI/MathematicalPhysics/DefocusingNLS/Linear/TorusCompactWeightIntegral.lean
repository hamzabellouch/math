import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzNormSquare
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationWeighted

namespace OAI

/-! # Exact weighted physical integration for a compactly supported torus coefficient -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance torusCompactWeightMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusCompactWeightProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem separatedSchwartz_torus_weighted_integral (L R : ℝ) (hL : 0 < L)
    (hLR : 2 * R < 2 * Real.pi * L) (K : 𝓢(E, ℂ))
    (hK : ∀ y : E, R < ‖y‖ → K y = 0) (u : C(T, ℂ)) :
    (2 * Real.pi * L) ^ 12 * (∫ x : T,
      ‖schwartzPeriodizedTorus (periodizationRescale L hL K) x * u x‖ ^ 2) =
      ∫ y : E, ‖K y * u (unitTorusProjection ((2 * Real.pi * L)⁻¹ • y))‖ ^ 2 := by
  let D := 2 * Real.pi * L
  have hD : 0 < D := by dsimp only [D]; positivity
  let e : C(E, ℂ) :=
    ⟨fun x => (‖u (unitTorusProjection x)‖ ^ 2 : ℝ), by
      exact Complex.continuous_ofReal.comp
        ((u.continuous.comp unitTorusProjection_isOpenQuotientMap.continuous).norm.pow 2)⟩
  have he : ∀ x, ‖e x‖ ≤ ‖u‖ ^ 2 := by
    intro x
    change ‖((‖u (unitTorusProjection x)‖ ^ 2 : ℝ) : ℂ)‖ ≤ ‖u‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (u.norm_coe_le_norm _) 2
  have hp : ∀ (x : E) (n : frequencyLattice), e (x + n) = e x := by
    intro x n
    change Complex.ofReal (‖u (unitTorusProjection (x + n))‖ ^ 2) =
      Complex.ofReal (‖u (unitTorusProjection x)‖ ^ 2)
    rw [unitTorusProjection_add_lattice]
  have hw := schwartzPeriodization_weighted_integral
    (periodizationRescale L hL (schwartzNormSquare K)) e (‖u‖ ^ 2) (sq_nonneg _) he hp
  have hleft : Complex.ofReal (∫ x : T,
      ‖schwartzPeriodizedTorus (periodizationRescale L hL K) x * u x‖ ^ 2) =
      ∫ x in frequencyCell, e x * schwartzPeriodization (periodizationRescale L hL (schwartzNormSquare K)) x := by
    rw [← integral_complex_ofReal, unitTorus_integral_eq_frequencyCell]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [schwartzPeriodizedTorus_projection, separatedSchwartz_periodization_normSquare L R hL hLR K hK]
    rw [norm_mul, mul_pow, Complex.ofReal_mul]
    dsimp only [e, ContinuousMap.coe_mk]
    ring
  let F : E → ℝ := fun y => ‖K y * u (unitTorusProjection (D⁻¹ • y))‖ ^ 2
  have hfun : (fun x : E => e x * periodizationRescale L hL (schwartzNormSquare K) x) =
      fun x => (F (D • x) : ℂ) := by
    funext x
    change (‖u (unitTorusProjection x)‖ ^ 2 : ℝ) *
      periodizationRescale L hL (schwartzNormSquare K) x = _
    rw [periodizationRescale_apply, schwartzNormSquare_apply]
    dsimp only [F]
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul, norm_mul, mul_pow, Complex.ofReal_mul]
    ring
  rw [hfun, integral_complex_ofReal] at hw
  rw [Measure.integral_comp_smul_of_nonneg volume F D (hR := hD.le)] at hw
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hw
  have hr := Complex.ofReal_injective (hleft.trans hw)
  change D ^ 12 * _ = ∫ y : E, F y
  rw [hr]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 12 hD.ne'), one_mul]

end DefocusingNLS

end OAI
