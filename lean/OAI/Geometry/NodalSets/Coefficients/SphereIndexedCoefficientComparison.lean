import OAI.Geometry.NodalSets.Spectral.SphereIndexedRayleigh
import OAI.Geometry.NodalSets.Spectral.SphereRayleighComparison

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section
local instance sphereIndexedComparisonMeasurable : MeasurableSpace Base := borel Base
local instance sphereIndexedComparisonBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereIndexedEigenvalue_le_of_rayleigh (d b : SphereEnergyData)
    (hd : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (hb : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ b.density (sphereChartCoordMap p x)))
    (c : ℝ) (hc : 0 ≤ c)
    (hcomp : ∀ u : sphereSmoothFunctions, u ≠ 0 →
      sphereRayleighQuotient b.tensor b.density u ≤ c*sphereRayleighQuotient d.tensor d.density u)
    (N : ℕ) : sphereIndexedEigenvalue b N ≤ c*sphereIndexedEigenvalue d N := by
  obtain ⟨V,hV,hdim,hVbound⟩ := (sphereIndexedEigenvalue_minmax d hd N).1
  obtain ⟨x,hx,hx0,hxlo⟩ := (sphereIndexedEigenvalue_minmax b hb N).2.1 V hV hdim
  exact hxlo.trans ((hcomp x hx0).trans (mul_le_mul_of_nonneg_left (hVbound x hx hx0) hc))

theorem sphereIndexedEigenvalue_ge_of_rayleigh (d b : SphereEnergyData)
    (hd : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (hb : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ b.density (sphereChartCoordMap p x)))
    (c : ℝ) (hc : 0 ≤ c)
    (hcomp : ∀ u : sphereSmoothFunctions, u ≠ 0 →
      c*sphereRayleighQuotient d.tensor d.density u ≤ sphereRayleighQuotient b.tensor b.density u)
    (N : ℕ) : c*sphereIndexedEigenvalue d N ≤ sphereIndexedEigenvalue b N := by
  obtain ⟨V,hV,hdim,hVbound⟩ := (sphereIndexedEigenvalue_minmax b hb N).1
  obtain ⟨x,hx,hx0,hxlo⟩ := (sphereIndexedEigenvalue_minmax d hd N).2.1 V hV hdim
  exact (mul_le_mul_of_nonneg_left hxlo hc).trans ((hcomp x hx0).trans (hVbound x hx hx0))

theorem sphere_finite_norm_indexed_eigenvalue_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ eta > 0, ∀ b : SphereEnergyData,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
      ∀ N : ℕ,
        (1-eps)/(1+eps)*sphereIndexedEigenvalue d N ≤ sphereIndexedEigenvalue b N ∧
        sphereIndexedEigenvalue b N ≤ (1+eps)/(1-eps)*sphereIndexedEigenvalue d N := by
  obtain ⟨eta,heta,hcomp⟩ := sphere_finite_norm_rayleigh_comparison P hcover
    d.tensor d.smooth d.symm d.pos d.density hd d.positive eps heps heps1
  refine ⟨eta,heta,?_⟩
  intro b hb hdist N
  have hdloc (p) := (hd.comp (sphereChartCoordMap_smooth p)).contDiff
  have hbloc (p) := (hb.comp (sphereChartCoordMap_smooth p)).contDiff
  have hc (u : sphereSmoothFunctions) (hu : u ≠ 0) := hcomp b.tensor b.density
    b.smooth b.symm b.pos hb b.positive hdist u u.property (fun h ↦ hu (Subtype.ext h))
  constructor
  · exact sphereIndexedEigenvalue_ge_of_rayleigh d b hdloc hbloc _
      (div_nonneg (by linarith) (by linarith)) (fun u hu ↦ (hc u hu).1) N
  · exact sphereIndexedEigenvalue_le_of_rayleigh d b hdloc hbloc _
      (div_nonneg (by linarith) (by linarith)) (fun u hu ↦ (hc u hu).2) N

end
end Yau.Target

end OAI
