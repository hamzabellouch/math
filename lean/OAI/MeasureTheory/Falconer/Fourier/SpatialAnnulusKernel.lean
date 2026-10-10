import OAI.MeasureTheory.Falconer.Fourier.PlaneFourierNonstationary
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap

noncomputable def spatialInnerBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Plane) :=
  ⟨δ/2, δ, half_pos hδ, half_lt_self hδ⟩

noncomputable def spatialOuterBump (L : ℝ) (hL : 0 < L) : ContDiffBump (0 : Plane) :=
  ⟨L, L+1, hL, by linarith⟩

noncomputable def spatialAnnulusKernel (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (z : Plane) : ℂ :=
  ↑(spatialOuterBump L hL z * (1-spatialInnerBump δ hδ z) * (‖z‖^j)⁻¹)

theorem spatialAnnulusKernel_smooth (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ContDiff ℝ ∞ (spatialAnnulusKernel δ L hδ hL j) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : spatialAnnulusKernel δ L hδ hL j =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [(spatialInnerBump δ hδ).eventuallyEq_one] with z hz
      simp [spatialAnnulusKernel, hz]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun z : Plane => (‖z‖^j)⁻¹) z :=
      ((contDiffAt_norm ℝ hz).pow j).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (((spatialOuterBump L hL).contDiffAt.mul
        (contDiffAt_const.sub (spatialInnerBump δ hδ).contDiffAt)).mul hn)

theorem spatialAnnulusKernel_compact (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : HasCompactSupport (spatialAnnulusKernel δ L hδ hL j) := by
  exact (((spatialOuterBump L hL).hasCompactSupport.mul_right).mul_right).comp_left
    (map_zero Complex.ofRealCLM)

theorem spatialAnnulusKernel_eq (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {z : Plane} (hz₁ : δ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ L) :
    spatialAnnulusKernel δ L hδ hL j z = ↑((‖z‖^j)⁻¹) := by
  have hi : spatialInnerBump δ hδ z = 0 :=
    (spatialInnerBump δ hδ).zero_of_le_dist (by simpa [spatialInnerBump] using hz₁)
  have ho : spatialOuterBump L hL z = 1 :=
    (spatialOuterBump L hL).one_of_mem_closedBall (by simpa [spatialOuterBump] using hz₂)
  simp [spatialAnnulusKernel, hi, ho]

noncomputable def spatialAnnulusSchwartz (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Plane, ℂ) :=
  (spatialAnnulusKernel_compact δ L hδ hL j).toSchwartzMap
    (spatialAnnulusKernel_smooth δ L hδ hL j)

end PlanarFalconer

end OAI
