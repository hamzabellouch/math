import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeEnergy

namespace OAI

/-! Exact variational bottom of the manufactured planar well on its
closed Sobolev graph. This is an analytic component of the continuum
construction; it does not assert the hardness reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance : BorelSpace PlanarPosition := ⟨rfl⟩
local instance : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem mode_mass : ‖mode.val.1‖ ^ 2 = originalIntegral (fun x => planarResolventMode x ^ 2) := by
  rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mode_memLp.coeFn_toLp] with x hx
  change inner ℝ (mode_memLp.toLp planarResolventMode x)
    (mode_memLp.toLp planarResolventMode x) = _
  rw [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem mode_kinetic : ‖mode.val.2‖ ^ 2 =
    ∑ a : Fin 2, originalIntegral (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) := by
  have hi (a : Fin 2) : Integrable (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) :=
    (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
      (planarResolventMode_partial_square_integrable (planarAxis a))
  simp_rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    ← integral_finsetSum Finset.univ (fun a _ => hi a)]
  apply integral_congr_ae
  filter_upwards [mode_grad_memLp.coeFn_toLp] with x hx
  change inner ℝ (mode_grad_memLp.toLp (grad planarResolventMode) x)
    (mode_grad_memLp.toLp (grad planarResolventMode) x) = _
  rw [hx, real_inner_self_eq_norm_sq, grad_norm_sq]

theorem mode_form : form mode.val = planarTestForm manufacturedPlanarWell planarResolventMode := by
  unfold form planarTestForm
  rw [mode_kinetic]
  apply congrArg₂ (· + ·)
  · rfl
  · change inner ℝ modeTarget.1 (wellMultiplier modeTarget.1) =
      originalIntegral (fun x => manufacturedPlanarWell x * planarResolventMode x ^ 2)
    rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [mode_memLp.coeFn_toLp, wellMultiply_ae modeTarget.1] with x hx hw
    change inner ℝ (modeTarget.1 x) (wellMultiply modeTarget.1 x) = _
    change modeTarget.1 x = planarResolventMode x at hx
    rw [hw, hx, RCLike.inner_apply, conj_trivial]
    ring

theorem form_smul (c : ℝ) (u : Target) : form (c • u) = c ^ 2 * form u := by
  change (1 / 2 : ℝ) * ‖c • u.2‖ ^ 2 + inner ℝ (c • u.1) (wellMultiplier (c • u.1)) = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  unfold form
  ring

theorem mode_energy : form mode.val = -(1 / 2 : ℝ) * ‖mode.val.1‖ ^ 2 := by
  rw [mode_form, mode_mass]
  exact planarResolventMode_energy

theorem mode_mass_positive : 0 < ‖mode.val.1‖ ^ 2 := by
  rw [mode_mass]
  exact planarResolventMode_square_integral_positive

def normalizedMode : Sobolev := (Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode

theorem normalizedMode_mass : ‖normalizedMode.val.1‖ ^ 2 = 1 := by
  change ‖(Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode.val.1‖ ^ 2 = 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt mode_mass_positive.le, inv_mul_cancel₀ mode_mass_positive.ne']

theorem normalizedMode_energy : form normalizedMode.val = -(1 / 2 : ℝ) := by
  change form ((Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode.val) = _
  rw [form_smul, mode_energy, inv_pow, Real.sq_sqrt mode_mass_positive.le]
  calc
    _ = -(1 / 2 : ℝ) * ((‖mode.val.1‖ ^ 2)⁻¹ * ‖mode.val.1‖ ^ 2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ mode_mass_positive.ne', mul_one]

def groundEnergy : EReal :=
  sInf {e | ∃ u : Sobolev, ‖u.val.1‖ ^ 2 = 1 ∧ e = (form u.val : EReal)}

/-- Exact manufactured-well bottom, proved without a published spectral input. -/
theorem groundEnergy_eq : groundEnergy = ((-1 / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · have h := sInf_le (show (form normalizedMode.val : EReal) ∈
        {e | ∃ u : Sobolev, ‖u.val.1‖ ^ 2 = 1 ∧ e = (form u.val : EReal)} from
      ⟨normalizedMode, normalizedMode_mass, rfl⟩)
    simpa only [groundEnergy, normalizedMode_energy, neg_div] using h
  · apply le_sInf
    rintro e ⟨u, hu, rfl⟩
    have h := form_lower u
    rw [hu, mul_one] at h
    simpa only [neg_div] using (EReal.coe_le_coe h)

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
