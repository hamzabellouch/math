import Mathlib.Topology.UniformSpace.UniformConvergence
import OAI.Geometry.NodalSets.Charts.SphereIndexedContinuity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

theorem sphereCoefficientDistance_mono_order (P : Finset Base) (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J K : ℕ) (hJK : J ≤ K) :
    sphereCoefficientDistance P J d.tensor d.density b.tensor b.density ≤
      sphereCoefficientDistance P K d.tensor d.density b.tensor b.density :=
  finiteChartDerivativeSize_mono_order P sphereAtlasCore_compact hJK _
    (fun p _ ↦ (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p))

theorem sphereCoefficientDistance_density_bound (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J : ℕ) (x : Base) :
    |b.density x-d.density x| ≤ sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  obtain ⟨p,hp,z,hz,rfl⟩ := hcover x
  exact (norm_snd_le (intrinsicChartCoefficient b.tensor b.density p z-
    intrinsicChartCoefficient d.tensor d.density p z)).trans
    (sphereCoefficientDistance_value_bound P J d.tensor b.tensor d.density b.density
      (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
      (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
      p hp z hz)

theorem sphere_finite_norm_density_uniform_convergence (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) (J : ℕ)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    TendstoUniformly (fun j ↦ (b j).density) d.density atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with j hj x
  simpa only [Real.dist_eq,abs_sub_comm] using
    (sphereCoefficientDistance_density_bound P hcover d (b j) hd (hb j) J x).trans_lt hj

theorem sphere_finite_norm_indexed_eigenvalue_convergence (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) (J N : ℕ)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereIndexedEigenvalue (b j) N) atTop (𝓝 (sphereIndexedEigenvalue d N)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨eta,heta,H⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d hd N eps heps
  filter_upwards [ht.eventually (gt_mem_nhds heta)] with j hj
  simpa only [Real.dist_eq] using H (b j) (hb j)
    ((sphereCoefficientDistance_mono_order P d (b j) hd (hb j) 0 J (Nat.zero_le J)).trans_lt hj)

end
end Yau.Target

end OAI
