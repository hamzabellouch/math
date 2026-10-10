import Mathlib.Analysis.Calculus.ContDiff.Bounds
import OAI.Geometry.NodalSets.Charts.ChartPushforward

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma chart_comp_derivative_bound (F : OpenPartialHomeomorph Coord Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (u : Coord → ℂ)
    (hu : ContDiffOn ℝ ∞ u F.source) (z : Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D : ℝ)
    (hC : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i u (F.symm z)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : Coord → Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (u ∘ F.symm) z‖ ≤ k.factorial * C * D^k := by
  have h := norm_iteratedFDerivWithin_comp_le hu hF (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
    F.open_source.uniqueDiffOn F.open_target.uniqueDiffOn (fun _ hx ↦ F.map_target hx) hz
    (C := C) (D := D)
  simp only [iteratedFDerivWithin_of_isOpen _ F.open_source (F.map_target hz),
    iteratedFDerivWithin_of_isOpen _ F.open_target hz] at h
  exact h hC hD

theorem chart_wave_size_transfer (F : OpenPartialHomeomorph Coord Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (u : Coord → ℂ)
    (hu : ContDiff ℝ ∞ u) (z : Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D E N : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hsize : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i u (F.symm z)‖ ≤ C*N^i*E)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : Coord → Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (chartPushforward F u) z‖ ≤ (k.factorial*C*D^k)*N^k*E := by
  rw [chartPushforward_derivative F u z hz k]
  have h := chart_comp_derivative_bound F hF u hu.contDiffOn z hz k (C*N^k*E) D
    (fun i hi ↦ (hsize i hi).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hi) hC) hE)) hD
  convert h using 1
  ring

theorem chart_residual_bound_transfer (F : OpenPartialHomeomorph Coord Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (R : Coord → ℂ)
    (hR : ContDiffOn ℝ ∞ R F.source) (z : Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D E N K : ℝ)
    (hres : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i R (F.symm z)‖ ≤ C*N^(-K)*E)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : Coord → Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (R ∘ F.symm) z‖ ≤ (k.factorial*C*D^k)*N^(-K)*E := by
  have h := chart_comp_derivative_bound F hF R hR z hz k (C*N^(-K)*E) D hres hD
  convert h using 1
  ring

end
end Yau.Geometry

end OAI
