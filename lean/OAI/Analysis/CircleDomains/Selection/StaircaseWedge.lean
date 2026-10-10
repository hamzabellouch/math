import OAI.Analysis.CircleDomains.Selection.WedgeMean
import OAI.Analysis.CircleDomains.Selection.ShiftedStaircase

namespace OAI

/-!
# Expected wedge of actual staircase coordinates

This instantiates the averaging bound with the constructed smooth
staircase family. After division by `h²`, the error is proportional to
`h`, uniformly in the transition width.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_shiftedStaircase_value {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    Continuous (fun θ => shiftedStaircase h δ θ x) := by
  unfold shiftedStaircase
  exact (((contDiff_smoothStaircase hh hδ hδh).continuous.comp
    (continuous_const.sub continuous_id)).add continuous_id).sub continuous_const

/-- The finite-transfer wedge bound for two independently shifted actual
staircases, prior to summing over coordinate pairs and domain points. -/
theorem average_staircase_wedge_le (u v c : ℝ × ℝ) (x y : ℝ)
    {h δ χ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    (∫ z in Icc 0 h ×ˢ Icc 0 h,
      |planarWedge
        (((1 - χ) + χ * deriv (shiftedStaircase h δ z.1) x) • u +
          (shiftedStaircase h δ z.1 x - x) • c)
        (((1 - χ) + χ * deriv (shiftedStaircase h δ z.2) y) • v +
          (shiftedStaircase h δ z.2 y - y) • c)| ∂volume.prod volume) / h ^ 2 ≤
      |planarWedge u v| + h * (|planarWedge u c| + |planarWedge c v|) := by
  let q := fun θ => (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x
  let p := fun θ => (1 - χ) + χ * deriv (shiftedStaircase h δ θ) y
  let r := fun θ => shiftedStaircase h δ θ x - x
  let s := fun θ => shiftedStaircase h δ θ y - y
  have hq : Continuous q := continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh x))
  have hp : Continuous p := continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh y))
  have hr : Continuous r := (continuous_shiftedStaircase_value hh hδ hδh x).sub continuous_const
  have hs : Continuous s := (continuous_shiftedStaircase_value hh hδ hδh y).sub continuous_const
  have hq0 (θ : ℝ) : 0 ≤ q θ :=
    add_nonneg (sub_nonneg.mpr hχ1)
      (mul_nonneg hχ0 (deriv_shiftedStaircase_nonneg hh hδ θ x))
  have hp0 (θ : ℝ) : 0 ≤ p θ :=
    add_nonneg (sub_nonneg.mpr hχ1)
      (mul_nonneg hχ0 (deriv_shiftedStaircase_nonneg hh hδ θ y))
  have hqm : (∫ θ in Icc 0 h, q θ) = h := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh.le]
    exact integral_shiftedStaircase_cutoff_multiplier hh hδ hδh x χ
  have hpm : (∫ θ in Icc 0 h, p θ) = h := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh.le]
    exact integral_shiftedStaircase_cutoff_multiplier hh hδ hδh y χ
  have hbound := integral_cutoff_wedge_le u v c hh.le hq hp hr hs
    (fun θ _ => hq0 θ) (fun θ _ => hp0 θ)
    (fun θ _ => abs_shiftedStaircase_sub_le hh δ θ x)
    (fun θ _ => abs_shiftedStaircase_sub_le hh δ θ y) hqm hpm
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  exact hbound.trans_eq (by ring)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
