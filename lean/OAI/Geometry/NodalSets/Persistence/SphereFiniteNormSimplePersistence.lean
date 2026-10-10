import OAI.Geometry.NodalSets.Charts.SphereIndexedGapContinuity
import OAI.Geometry.NodalSets.Charts.SphereIndexedGapSimplicityLemmas
import OAI.Geometry.NodalSets.Spectral.SphereIndexedSpectralCoverage

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_norm_simple_eigenvalue_persistence (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) → ∃ c : ℝ, v=c • u)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
      ∃ eta > 0, ∀ b : SphereEnergyData,
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
        sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
        |sphereIndexedEigenvalue b N-lam| < delta ∧
        sphereIndexedEigenvalue b N ∈ Set.Icc (lam/2) (2*lam) ∧
        ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
          sphereWeightedPairing b.density v v=1 ∧
          (∀ p z, -intrinsicWeightedChartOperator b.tensor b.density v p z =
            sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm z)) ∧
          ∀ w : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w →
            (∀ p z, -intrinsicWeightedChartOperator b.tensor b.density w p z =
              sphereIndexedEigenvalue b N*w ((extChartAt (𝓡 4) p).symm z)) →
            ∃ c : ℝ, w=c • v := by
  let U : SphereEnergySmooth d := (⟨u,hu⟩ : sphereSmoothFunctions)
  have hU : U ≠ 0 := fun h ↦ hu0 (congrArg (fun z : SphereEnergySmooth d ↦
    (SphereEnergySmooth.toSmooth d z : Base → ℝ)) h)
  obtain ⟨N,hN⟩ := sphere_smooth_intrinsic_eigenvalue_index d hd U hU lam he
  have hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)) :=
    fun p ↦ (hd.comp (sphereChartCoordMap_smooth p)).contDiff
  obtain ⟨hl,hr⟩ := sphere_simple_indexed_strict_gaps d hrho u hu lam hsimple N hN
  obtain ⟨eta,heta,H⟩ := sphere_finite_norm_indexed_gaps_persist P hcover d hd N
    (by simpa only [hN] using hl) (by simpa only [hN] using hr)
    (min delta (lam/2)) (lt_min hdelta (by positivity))
  refine ⟨N,hN,eta,heta,?_⟩
  intro b hb hdist
  obtain ⟨hclose,hleft,hright⟩ := H b hb hdist
  rw [hN] at hclose
  refine ⟨hclose.trans_le (min_le_left _ _),?_,sphere_indexed_intrinsic_simple_of_gaps b hb N hleft hright⟩
  have hh := abs_lt.mp (hclose.trans_le (min_le_right _ _))
  exact ⟨by linarith,by linarith⟩

end
end Yau.Target

end OAI
