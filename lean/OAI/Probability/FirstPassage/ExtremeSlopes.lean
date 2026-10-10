import OAI.Probability.FirstPassage.Supports
import Mathlib.Analysis.Convex.Deriv

namespace OAI

namespace PlanarFPP
open Set

noncomputable def leftSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Iio 0) 0
noncomputable def rightSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Ioi 0) 0

theorem extreme_slopes_ordered (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    leftSlope φ ≤ rightSlope φ :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

theorem subgradient_of_between_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (a : ℝ) (hleft : leftSlope φ ≤ a) (hright : a ≤ rightSlope φ) :
    ∀ t, φ 0 + a * t ≤ φ t := by
  intro t
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · have hbound := hφ.rightDeriv_le_slope_of_mem_interior (by simp) (by simp) ht
    have ha : a ≤ (φ t - φ 0) / t := by
      exact le_trans hright (by simpa [rightSlope, slope_def_field] using hbound)
    have := (le_div_iff₀ ht).mp ha
    linarith
  · simp
  · have hbound := hφ.slope_le_leftDeriv_of_mem_interior (by simp) (by simp) ht
    have ha : (φ 0 - φ t) / (0 - t) ≤ a := by
      exact le_trans (by simpa [leftSlope, slope_def_field] using hbound) hleft
    have := (div_le_iff₀ (show 0 < 0 - t by linarith)).mp ha
    linarith

theorem extreme_subgradients (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    (∀ t, φ 0 + leftSlope φ * t ≤ φ t) ∧
    (∀ t, φ 0 + rightSlope φ * t ≤ φ t) := by
  have horder := extreme_slopes_ordered φ hφ
  exact ⟨subgradient_of_between_slopes φ hφ _ le_rfl horder,
    subgradient_of_between_slopes φ hφ _ horder le_rfl⟩

theorem extreme_slopes_contact (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    HasDerivWithinAt φ (leftSlope φ) (Iio 0) 0 ∧
    HasDerivWithinAt φ (rightSlope φ) (Ioi 0) 0 := by
  exact ⟨hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp),
    hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)⟩

theorem convex_transverse_profile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z) :
    ConvexOn ℝ univ (fun t : ℝ => μ (u + t • e)) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * v + b * w) • e = a • (u + v • e) + b • (u + w • e) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
      ← add_smul, hab, one_smul, ← add_smul]
  rw [heq]
  exact (hadd _ _).trans_eq (by rw [hhom a ha, hhom b hb])

theorem extreme_supports {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e) :
    let φ := fun t : ℝ => μ (u + t • e)
    (∀ z, coordinateSupport x r (μ u) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport x r (μ u) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport x r (μ u) (leftSlope φ) u = μ u ∧
    coordinateSupport x r (μ u) (rightSlope φ) u = μ u := by
  dsimp only
  obtain ⟨hl, hr⟩ := extreme_subgradients _ (convex_transverse_profile μ u e hadd hhom)
  have hls := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hl)
  have hrs := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hr)
  exact ⟨hls.1, hrs.1, hls.2, hrs.2⟩

end PlanarFPP

end OAI
