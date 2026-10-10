import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientNormConvergence

namespace OAI

noncomputable section

namespace Yau.Target

open Manifold Yau.Geometry
open scoped ContDiff

theorem sphereCoefficientDistance_mono_atlas (P Q : Finset Base) (hPQ : P ⊆ Q)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J : ℕ) : sphereCoefficientDistance P J d.tensor d.density b.tensor b.density ≤
      sphereCoefficientDistance Q J d.tensor d.density b.tensor b.density := by
  let f := fun p y ↦ intrinsicChartCoefficient b.tensor b.density p y-intrinsicChartCoefficient d.tensor d.density p y
  have hf (p : Base) : ContDiff ℝ ∞ (f p) :=
    (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
  apply finiteChartDerivativeSize_le
  · exact finiteChartDerivativeSize_nonneg Q sphereAtlasCore_compact J f (fun p _ ↦ hf p)
  · intro p hp i hi y hy
    exact norm_le_finiteChartDerivativeSize Q sphereAtlasCore_compact J f
      (fun p _ ↦ hf p) p (hPQ hp) i hi y hy

open Manifold Yau.Geometry Filter
open scoped ContDiff Topology

theorem sphere_finite_norm_lower_order_convergence (P : Finset Base)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (J K : ℕ) (hJK : J ≤ K)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P K d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0) := by
  apply squeeze_zero _ _ ht
  · intro j
    exact sphereCoefficientDistance_nonneg P J d.tensor (b j).tensor d.density (b j).density
      (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
      (fun p _ ↦ intrinsic_coefficient_chart_smooth (b j).tensor (b j).smooth (b j).symm (b j).pos
        (b j).density (hb j) p)
  · intro j
    exact sphereCoefficientDistance_mono_order P d (b j) hd (hb j) J K hJK

end Yau.Target

end

end OAI
