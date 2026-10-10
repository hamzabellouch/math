import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolevDuality
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarDistributionAxes
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGapFromUniqueness

namespace OAI

/-! Uniqueness and the actual manufactured planar ground gap, proved on the
full closed Sobolev graph without the published spectral hypothesis. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev

local instance instPlanarGroundUniquenessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarGroundUniquenessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarGroundUniquenessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem zero_ground_form_multiple (u : Sobolev) (hzero : shiftedForm u.val = 0) :
    ∃ c : ℝ, u.val.1 = c • mode.val.1 := by
  have hloc : LocallyIntegrable (fun x => u.val.1 x/planarResolventMode x) := by
    have hli : LocallyIntegrable (fun x : PlanarPosition => u.val.1 x) :=
      (Lp.memLp u.val.1).locallyIntegrable (by norm_num)
    have hi : Continuous (fun x : PlanarPosition => (planarResolventMode x)⁻¹) :=
      planarResolventMode_C7.continuous.inv₀
      (fun x => (planarResolventMode_positive x).ne')
    have hh : LocallyIntegrable (fun x : PlanarPosition => u.val.1 x*(planarResolventMode x)⁻¹) :=
      LocallyIntegrable.mul_continuous hi hli
    simpa only [div_eq_mul_inv] using hh
  obtain ⟨c,hc⟩ := planar_zero_axis_distribution_constant
    (fun x => u.val.1 x/planarResolventMode x) hloc (fun ψ hψ hψc a =>
      zero_ground_form_axis_distribution u hzero ψ (hψ.of_le (by simp)) hψc a)
  refine ⟨c,Lp.ext ?_⟩
  have hmode : mode.val.1 =ᵐ[volume] planarResolventMode := mode_memLp.coeFn_toLp
  filter_upwards [hc,hmode,Lp.coeFn_smul c mode.val.1] with x hx hm hs
  rw [hs]
  change u.val.1 x = c*mode.val.1 x
  rw [hm]
  exact (div_eq_iff (planarResolventMode_positive x).ne').mp hx

theorem zero_ground_form_orthogonal (u : Sobolev) (hzero : shiftedForm u.val = 0)
    (ho : inner ℝ u.val.1 normalizedMode.val.1 = 0) : u = 0 := by
  obtain ⟨c,hu⟩ := zero_ground_form_multiple u hzero
  rw [hu] at ho
  change inner ℝ (c • mode.val.1) ((Real.sqrt (‖mode.val.1‖^2))⁻¹ • mode.val.1) = 0 at ho
  rw [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq] at ho
  have hcoef : (Real.sqrt (‖mode.val.1‖^2))⁻¹*‖mode.val.1‖^2 ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr mode_mass_positive).ne') mode_mass_positive.ne'
  have hc : c = 0 := (mul_eq_zero.mp ho).resolve_right hcoef
  have hu0 : u.val.1 = 0 := by simpa only [hc,zero_smul] using hu
  have hgrad : ‖u.val.2‖^2 = 0 := by
    simp only [shiftedForm,form,hu0,map_zero,inner_zero_left,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero,add_zero] at hzero
    linarith
  have hg0 : u.val.2 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hgrad)
  apply Subtype.ext
  exact Prod.ext hu0 hg0

/-- Positive gap above the actual manufactured well's attained ground mode. -/
theorem manufacturedPlanarWell_gap_proved :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 normalizedMode.val.1 = 0 →
      ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val :=
  planar_gap_of_ground_uniqueness zero_ground_form_orthogonal

end ContinuumCoulomb.PlanarSobolev

end

end OAI
