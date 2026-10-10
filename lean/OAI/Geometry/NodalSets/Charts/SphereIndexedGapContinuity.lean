import OAI.Geometry.NodalSets.Charts.SphereIndexedContinuity
import OAI.Geometry.NodalSets.Charts.SphereIndexedGapSimplicityLemmas

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_norm_indexed_gaps_persist (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ)
    (hleft : ∀ M : ℕ, M < N → sphereIndexedEigenvalue d M < sphereIndexedEigenvalue d N)
    (hright : sphereIndexedEigenvalue d N < sphereIndexedEigenvalue d (N+1))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eta > 0, ∀ b : SphereEnergyData,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
      |sphereIndexedEigenvalue b N-sphereIndexedEigenvalue d N| < delta ∧
      (∀ M : ℕ, M < N → sphereIndexedEigenvalue b M < sphereIndexedEigenvalue b N) ∧
      sphereIndexedEigenvalue b N < sphereIndexedEigenvalue b (N+1) := by
  let g : ℝ := if N=0 then sphereIndexedEigenvalue d (N+1)-sphereIndexedEigenvalue d N
    else min (sphereIndexedEigenvalue d N-sphereIndexedEigenvalue d (N-1))
      (sphereIndexedEigenvalue d (N+1)-sphereIndexedEigenvalue d N)
  have hg : 0 < g := by
    dsimp [g]
    split_ifs with hN
    · linarith
    · exact lt_min (sub_pos.mpr (hleft (N-1) (by omega))) (sub_pos.mpr hright)
  obtain ⟨eps,heps,hepslt⟩ := exists_between (lt_min hdelta (div_pos hg (by norm_num : (0:ℝ)<3)))
  have hepsdelta : eps < delta := hepslt.trans_le (min_le_left _ _)
  have hepsg : 2*eps < g := by
    have hh : eps < g/3 := hepslt.trans_le (min_le_right _ _)
    linarith
  have hrightgap : 2*eps < sphereIndexedEigenvalue d (N+1)-sphereIndexedEigenvalue d N := by
    apply hepsg.trans_le
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact min_le_right _ _
  have hleftgap (hN : N ≠ 0) : 2*eps < sphereIndexedEigenvalue d N-sphereIndexedEigenvalue d (N-1) := by
    exact hepsg.trans_le (by dsimp [g]; rw [ite_eq_right hN]; exact min_le_left _ _)
  obtain ⟨eta₀,h₀,H₀⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d hd (N-1) eps heps
  obtain ⟨eta₁,h₁,H₁⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d hd N eps heps
  obtain ⟨eta₂,h₂,H₂⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d hd (N+1) eps heps
  refine ⟨min eta₀ (min eta₁ eta₂),lt_min h₀ (lt_min h₁ h₂),?_⟩
  intro b hb hdist
  have H0 := abs_lt.mp (H₀ b hb (hdist.trans_le (min_le_left _ _)))
  have H1 := H₁ b hb (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have H2 := abs_lt.mp (H₂ b hb (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨H1.trans hepsdelta,?_,?_⟩
  · intro M hM
    have hN : N ≠ 0 := by omega
    have hbmono := sphereIndexedEigenvalue_monotone b (fun p ↦ (hb.comp (sphereChartCoordMap_smooth p)).contDiff)
    apply (hbmono (show M ≤ N-1 by omega)).trans_lt
    have hh := hleftgap hN
    have HH := abs_lt.mp H1
    linarith
  · have HH := abs_lt.mp H1
    linarith

end
end Yau.Target

end OAI
