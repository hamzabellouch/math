import OAI.Geometry.NodalSets.Charts.SphereForcingJetNeighborhood
import OAI.Geometry.NodalSets.Charts.SphereGlobalNeighborhoodCompactness
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientNormConvergence

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Yau.Geometry Yau.Analysis Metric Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereFiniteNormCompactMeasurable : MeasurableSpace Base := borel Base
local instance sphereFiniteNormCompactBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_norm_indexed_compactness (d₀ : SphereEnergyData)
    (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density) (N n : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p z=x) ∧
      ∃ eta > 0, ∀ b : ℕ → SphereEnergyData,
        (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) →
        (∀ j, sphereCoefficientDistance P (n+6) d₀.tensor d₀.density (b j).tensor (b j).density < eta) →
        ∀ f : ∀ j, SphereWeightedL2 (b j),
          (∀ j, sphereL2Resolvent (b j) (f j)=(sphereIndexedEigenvalue (b j) N+1)⁻¹ • f j) →
          (∀ j, ‖f j‖=1) →
          ∃ u : ℕ → Base → ℝ,
            (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
            (∀ j, u j =ᵐ[sphereWeightedMeasure (b j).density] (f j : Base → ℝ)) ∧
            (∀ j, sphereWeightedPairing (b j).density (u j) (u j)=1) ∧
            (∀ j, u j ≠ 0) ∧
            ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
              ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
                (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
                  TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
                    (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
                (Tendsto (fun j ↦ sphereCoefficientDistance P (n+6) d₀.tensor d₀.density
                    (b j).tensor (b j).density) atTop (𝓝 0) →
                  sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0) := by
  have hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)) :=
    fun p ↦ (hd₀.comp (sphereChartCoordMap_smooth p)).contDiff
  obtain ⟨P,hP,eps,heps,H⟩ := sphere_eigen_global_neighborhood_compactness d₀ hrho₀
    (sphereIndexedEigenvalue d₀ N+1)⁻¹ n
  have hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x := by
    intro x
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv z,⟨z,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hz),rfl⟩,hzx⟩
  obtain ⟨eta₀,h₀,H₀⟩ := sphere_finite_norm_divergence_neighborhood P d₀ hd₀
    (sphereIndexedEigenvalue d₀ N) (n+6) eps heps
  obtain ⟨eta₁,h₁,H₁⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d₀ hd₀ N eta₀ h₀
  refine ⟨P,hP,min eta₀ eta₁,lt_min h₀ h₁,?_⟩
  intro b hb hdist f heigen hn
  have hrho (j : ℕ) (p : Base) : ContDiff ℝ ∞ (fun x ↦ (b j).density (sphereChartCoordMap p x)) :=
    ((hb j).comp (sphereChartCoordMap_smooth p)).contDiff
  have hmu (j : ℕ) : (sphereIndexedEigenvalue (b j) N+1)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    have hp := (sphereIndexedEigenvalue_minmax (b j) (hrho j) N).2.2
    linarith
  have hclose (j : ℕ) := H₀ (b j) (sphereIndexedEigenvalue (b j) N) (hb j)
    ((hdist j).trans_le (min_le_left _ _))
    (H₁ (b j) (hb j) ((sphereCoefficientDistance_mono_order P d₀ (b j) hd₀ (hb j) 0 (n+6) (by omega)).trans_lt
      ((hdist j).trans_le (min_le_right _ _))))
  have hchart := H b (fun j ↦ (sphereIndexedEigenvalue (b j) N+1)⁻¹) hrho hmu
    (fun j p hp x hx ds hds ↦ by
      have h := hclose j p hp x ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/128 ≤ 1)) hx) ds hds
      refine ⟨h.1,?_⟩
      change |partialJet (fun y ↦ (((sphereIndexedEigenvalue (b j) N+1)⁻¹)⁻¹-1) *
        (roundCoordDensity y*(b j).density (sphereChartCoordMap p y))) ds x-
        partialJet (fun y ↦ (((sphereIndexedEigenvalue d₀ N+1)⁻¹)⁻¹-1) *
          (roundCoordDensity y*d₀.density (sphereChartCoordMap p y))) ds x| ≤ eps
      simpa only [inv_inv,add_sub_cancel_right] using h.2.1)
    (fun j p hp x hx ↦ (hclose j p hp x
      ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/128 ≤ 1)) hx) [] (by simp)).2.2)
    f heigen hn
  obtain ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,hnorm⟩ := hchart
  refine ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,?_⟩
  intro hlim
  exact hnorm (sphere_finite_norm_density_uniform_convergence P hcover d₀ b hd₀ hb (n+6) hlim)

end
end Yau.Target

end OAI
