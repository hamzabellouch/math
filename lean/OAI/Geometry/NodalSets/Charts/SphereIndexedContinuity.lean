import OAI.Geometry.NodalSets.Coefficients.SphereIndexedCoefficientComparison

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem relative_comparison_absolute_neighborhood (a : ℝ) (ha : 0 ≤ a)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps > 0, eps < 1 ∧ ∀ b : ℝ,
      (1-eps)/(1+eps)*a ≤ b → b ≤ (1+eps)/(1-eps)*a → |b-a| < delta := by
  have hden : 0 < 2*a+delta+1 := by linarith
  obtain ⟨eps,heps,hepslt⟩ := exists_between
    (lt_min (by norm_num : (0:ℝ)<1/2) (div_pos hdelta hden))
  have hepshalf : eps < 1/2 := hepslt.trans_le (min_le_left _ _)
  have hsmall : eps*(2*a+delta+1) < delta := (lt_div_iff₀ hden).mp
    (hepslt.trans_le (min_le_right _ _))
  have hm : 0 < 1-eps := by linarith
  have hp : 0 < 1+eps := by linarith
  refine ⟨eps,heps,by linarith,?_⟩
  intro b hlo hhi
  rw [div_mul_eq_mul_div] at hlo hhi
  have hlo' := (div_le_iff₀ hp).mp hlo
  have hhi' := (le_div_iff₀ hm).mp hhi
  apply abs_lt.mpr
  constructor
  · by_contra h
    have hb : b ≤ a-delta := by linarith
    have hprod := mul_le_mul_of_nonneg_right hb hp.le
    nlinarith
  · by_contra h
    have hb : a+delta ≤ b := by linarith
    have hprod := mul_le_mul_of_nonneg_right hb hm.le
    nlinarith

theorem sphere_finite_norm_indexed_eigenvalue_continuity (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (N : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eta > 0, ∀ b : SphereEnergyData,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
      |sphereIndexedEigenvalue b N-sphereIndexedEigenvalue d N| < delta := by
  have hnonneg := (sphereIndexedEigenvalue_minmax d
    (fun p ↦ (hd.comp (sphereChartCoordMap_smooth p)).contDiff) N).2.2
  obtain ⟨eps,heps,heps1,habs⟩ := relative_comparison_absolute_neighborhood
    (sphereIndexedEigenvalue d N) hnonneg delta hdelta
  obtain ⟨eta,heta,hcomp⟩ := sphere_finite_norm_indexed_eigenvalue_comparison P hcover d hd eps heps heps1
  exact ⟨eta,heta,fun b hb hdist ↦ habs _ (hcomp b hb hdist N).1 (hcomp b hb hdist N).2⟩

end
end Yau.Target

end OAI
