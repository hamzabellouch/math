import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarProjectionGap

namespace OAI

/-! The same fixed isolated-well projection gap holds at every actual
planar site, by translation of test functions and Euclidean volume. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_add_right (f : PlanarPosition → ℝ) (u e x : PlanarPosition) :
    planarPartial (fun y => f (y+u)) e x = planarPartial f e (x+u) := by
  simp only [planarPartial, fderiv_comp_add_right]

theorem planarTestForm_translate (W f : PlanarPosition → ℝ) (u : PlanarPosition) :
    planarTestForm W (fun x => f (x+u)) =
      planarTestForm (fun x => W (x-u)) f := by
  unfold planarTestForm
  apply congrArg₂ (· + ·)
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [planarPartial_add_right]
    exact integral_add_right_eq_self (fun x => planarPartial f (planarAxis a) x ^ 2) u
  · rw [← integral_add_right_eq_self (fun x => W (x-u) * f x ^ 2) u]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [add_sub_cancel_right]

theorem manufacturedPlanarWell_translated_projection_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (u : PlanarPosition) (f : PlanarPosition → ℝ),
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ) + γ) * (∫ x, f x ^ 2) -
        γ * (∫ x, f x * normalizedPlanarMode (x-u))^2 ≤
          planarTestForm (fun x => manufacturedPlanarWell (x-u)) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_actual_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun u f hf hc => ?_⟩
  have hF : ContDiff ℝ 1 (fun x => f (x+u)) := hf.comp (contDiff_id.add contDiff_const)
  have hC : HasCompactSupport (fun x => f (x+u)) := hc.comp_homeomorph (Homeomorph.addRight u)
  have h := hgap (fun x => f (x+u)) hF hC
  have hm : (∫ x, f (x+u)^2) = ∫ x, f x^2 :=
    integral_add_right_eq_self (fun x => f x^2) u
  have hp : (∫ x, f (x+u) * normalizedPlanarMode x) =
      ∫ x, f x * normalizedPlanarMode (x-u) := by
    rw [← integral_add_right_eq_self (fun x => f x * normalizedPlanarMode (x-u)) u]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [add_sub_cancel_right]
  rwa [hm, hp, planarTestForm_translate] at h

end ContinuumCoulomb

end

end OAI
