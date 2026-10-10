import OAI.Geometry.NodalSets.Charts.SphereC1IntrinsicLimit
import OAI.Geometry.NodalSets.Charts.SphereFiniteNormIndexedCompactness
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientAtlasInclusionLemmas

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section
local instance sphereIntrinsicCompactMeasurable : MeasurableSpace Base := borel Base
local instance sphereIntrinsicCompactBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_norm_indexed_intrinsic_compactness (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p y=x) ∧
      ∃ eta > 0, ∀ (b : ℕ → SphereEnergyData),
        (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) →
        (∀ j, sphereCoefficientDistance P 8 d.tensor d.density (b j).tensor (b j).density < eta) →
        Tendsto (fun j ↦ sphereCoefficientDistance P 8 d.tensor d.density
          (b j).tensor (b j).density) atTop (𝓝 0) →
        ∀ u : ℕ → Base → ℝ,
          (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) →
          (∀ j, sphereWeightedPairing (b j).density (u j) (u j)=1) →
          (∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density (u j) p y =
            sphereIndexedEigenvalue (b j) N * u j ((extChartAt (𝓡 4) p).symm y)) →
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
            sphereWeightedPairing d.density v v=1 ∧ v ≠ 0 ∧
            (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
              sphereIndexedEigenvalue d N * v ((extChartAt (𝓡 4) p).symm y)) ∧
            ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
              ∀ p ∈ P, ∀ i : Fin 4,
                TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) [i])
                  (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 (1/256)) := by
  obtain ⟨P,hP,eta,heta,H⟩ := sphere_finite_norm_indexed_compactness d hd N 2
  refine ⟨P,hP,eta,heta,?_⟩
  intro b hb hdist hcoeff u hu hn he
  let U (j : ℕ) : SphereEnergySmooth (b j) := (⟨u j,hu j⟩ : sphereSmoothFunctions)
  let f (j : ℕ) : SphereWeightedL2 (b j) := sphereEnergyL2Linear (b j) (U j)
  have hfn (j : ℕ) : ‖f j‖=1 := by
    have h := sphereEnergyL2Linear_norm_sq (b j) (U j)
    change ‖f j‖^2=sphereWeightedPairing (b j).density (u j) (u j) at h
    rw [hn j] at h
    nlinarith [norm_nonneg (f j)]
  have hfe (j : ℕ) : sphereL2Resolvent (b j) (f j) =
      (sphereIndexedEigenvalue (b j) N+1)⁻¹ • f j := by
    have hnonzero : sphereEnergyL2Map (b j) (sphereEnergyToCompletion (b j) (U j)) ≠ 0 := by
      rw [sphereEnergyL2Map_coe]
      intro hz
      have hh := hfn j
      change ‖sphereEnergyL2Linear (b j) (U j)‖=1 at hh
      rw [hz,norm_zero] at hh
      norm_num at hh
    have h := (sphere_variational_eigen_to_resolvent (b j) (sphereIndexedEigenvalue (b j) N)
      (sphereEnergyToCompletion (b j) (U j)) hnonzero
      (sphere_smooth_intrinsic_eigen_to_variational (b j) (hb j) (U j) _ (he j))).2
    simpa only [sphereEnergyL2Map_coe] using h
  obtain ⟨u',hu',ha,_,_,v,hv,nu,hnu,ht,hjet,hnorm⟩ := H b hb hdist f hfe hfn
  have hsame : u'=u := by
    funext j
    apply sphere_continuous_eq_of_weighted_ae (b j) (u' j) (u j) (hu' j).continuous (hu j).continuous
    exact (ha j).trans (sphereWeighted_memLp (b j).density (b j).continuous
      (fun x ↦ ((b j).positive x).le) (u j) (hu j).continuous).coeFn_toLp
  subst u'
  have hvnorm := hnorm hcoeff
  have hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/256), sphereChartCoordMap p y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,y,(ball_subset_ball (by norm_num : (1:ℝ)/512 ≤ 1/256)) hy,hyx⟩
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hy),rfl⟩,hyx⟩
  have h0 := sphere_finite_norm_lower_order_convergence P d b hd hb 0 8 (by omega) hcoeff
  have hlam := sphere_finite_norm_indexed_eigenvalue_convergence P hcore d b hd hb 8 N hcoeff
  let V (j : ℕ) : SphereEnergySmooth d := (⟨u (nu j),hu (nu j)⟩ : sphereSmoothFunctions)
  have hreg := sphere_finite_norm_C1_intrinsic_limit P (1/256) (by norm_num) hcover d hd
    (fun j ↦ b (nu j)) (fun j ↦ hb (nu j)) V v hv.continuous hvnorm.2 ht
    (fun p hp i ↦ hjet p hp [i] (by simp))
    (h0.comp hnu.tendsto_atTop) (fun j ↦ sphereIndexedEigenvalue (b (nu j)) N)
    (sphereIndexedEigenvalue d N) (hlam.comp hnu.tendsto_atTop) (fun j ↦ he (nu j))
  exact ⟨v,hreg.1,hvnorm.1,hvnorm.2,hreg.2,nu,hnu,ht,fun p hp i ↦ hjet p hp [i] (by simp)⟩

end
end Yau.Target

end OAI
