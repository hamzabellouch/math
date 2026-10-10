import OAI.Analysis.CircleDomains.Topology.HeightCompactness
import OAI.Analysis.CircleDomains.Sobolev.HeightEnergyModulus
import OAI.Analysis.CircleDomains.Topology.HomeomorphicHeightBounds

namespace OAI

/-! Locally uniform compactness of the actual normalized conductivity
heights from their energy budget and common exterior disk. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem conductivity_height_subsequence
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun x => φ n (complexPlaneCoordinates x)))
    {B R : ℝ} (hB0 : 0 ≤ B) (hR : 0 < R)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∃ (v : C(ℂ, ℝ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop := by
  let f : ℕ → C(ℂ, ℝ) := fun n => ⟨fun z => (φ n z).im,
    Complex.continuous_im.comp (φ n).continuous⟩
  apply locally_uniform_height_subsequence f
    (homeomorphic_heights_equicontinuous φ D hB0 hI hB)
  intro z
  let S := max (2*R) ‖z‖
  refine ⟨S+R, ?_⟩
  intro n
  exact normalized_homeomorphic_height_bound harea hR (le_max_left _ _)
    (hh n) (hnorm n) z (mem_closedBall.mpr (by
      simpa only [dist_zero_right] using le_max_right (2*R) ‖z‖))

end CircleDomainRigidity

end

end OAI
