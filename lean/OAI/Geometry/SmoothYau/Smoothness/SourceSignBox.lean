import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsBoxIccSubsetOpen
import OAI.Geometry.SmoothYau.Geometry.ExistsGlobalBoxAmplifiedProfile
import OAI.Geometry.SmoothYau.Geometry.SphericalBaseProfileChartHessian

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

def sourceSignBox : Box (Fin 3) := Classical.choose exists_spherical_sign_box

lemma sourceSignBox_band (y : NormalWaveSpace)
    (hy : y ∈ normalWaveEquiv '' Box.Icc sourceSignBox) :
    (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) ∧
    sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < 1/8 :=
  Classical.choose_spec exists_spherical_sign_box y hy

def sourceSignRegion : Set (Sphere 3) :=
  (chartAt (Euclidean 3) sourcePole).symm '' (normalWaveEquiv '' Box.Ioo sourceSignBox)

lemma sourceSignRegion_band (q : Sphere 3) (hq : q ∈ sourceSignRegion) :
    (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo q ∧
      sphericalRadius sourceAxisOne sourceAxisTwo q < 1/8 := by
  obtain ⟨y,⟨x,hx,rfl⟩,rfl⟩ := hq
  exact sourceSignBox_band _ ⟨x,sourceSignBox.Ioo_subset_Icc hx,rfl⟩

def sourceProfileCoverage : Set NormalWaveSpace :=
  sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10)

lemma sourceProfileCoverage_compact : IsCompact sourceProfileCoverage :=
  sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (by norm_num)

lemma sourceSignBox_subset_coverage :
    normalWaveEquiv '' Box.Icc sourceSignBox ⊆ sourceProfileCoverage := by
  intro y hy
  apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num) y).mpr
  have hh := (sourceSignBox_band y hy).2
  linarith

def sphericalProfileMetricNeighborhood : Set (SmoothMetric (Euclidean 3) (Sphere 3)) :=
  {g | ∀ t : ℝ, ∀ y ∈ sourceProfileCoverage,
    hessianMargins (selfMetricFlat (sphereChartMetric g sourcePole) y)
      (actualCoordinateHessian (sphereChartMetric g sourcePole)
        (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
          (chartAt (Euclidean 3) sourcePole).symm) y)}

lemma sphericalProfileMetricNeighborhood_isNeighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ sphericalProfileMetricNeighborhood :=
  sphericalBaseProfile_uniform_neighborhood g₀ hg₀

lemma coordinateMetricGradient_ne_zero_of_fderiv
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (f : NormalWaveSpace → ℝ)
    (y : NormalWaveSpace) (hf : fderiv ℝ f y ≠ 0) :
    coordinateMetricGradient g f y ≠ 0 := by
  intro hz
  apply hf
  ext v
  have hh := coordinateMetricGradient_pairing g f y v
  rw [hz] at hh
  simpa using hh.symm

lemma source_baseProfile_sign_gradient
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (t : ℝ) :
    ∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
      coordinateMetricGradient (sphereChartMetric g sourcePole)
        (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
          (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 := by
  intro y hy
  obtain ⟨hr₀,hr₁⟩ := sourceSignBox_band y hy
  obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
  apply coordinateMetricGradient_ne_zero_of_fderiv
  apply sphericalBaseProfile_chart_fderiv_ne_zero g₀ hg₀ sourcePole
    sourceAxisOne sourceAxisTwo ha hb hab t y
  · rw [← sphericalRadius_chart_sq]
    nlinarith
  · rw [← sphericalRadius_chart_sq]
    have hn := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y)
    nlinarith

theorem exists_global_spherical_wave_profile
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    (t : ℝ) (ht : t ∈ Icc (1/5 : ℝ) (3/10)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ sourceSignRegion ∧
      (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < ε) ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 →
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y = 0 →
        ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
          ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian (sphereChartMetric g sourcePole)
            (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y v v) ∧
      (∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
        coordinateMetricGradient (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 ∧
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      T < ∫ x in Box.Icc sourceSignBox, profileFrequencyScale (sphereChartMetric g sourcePole)
        (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) (normalWaveEquiv x) := by
  let f := sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
    (chartAt (Euclidean 3) sourcePole).symm
  let G := sphereChartMetric g sourcePole
  obtain ⟨η,hη,henvelope⟩ := spherical_envelope_perturbation sourceSignRegion_band
  have htol : 0 < min ε η := lt_min hε hη
  have hnc : ∀ y ∈ sourceProfileCoverage, fderiv ℝ f y ≠ 0 → actualProfileStrict G f y := by
    intro y hy _
    exact hessianMargins_actualProfileStrict G f y (hg t y hy)
  have hcrit : ∀ y ∈ sourceProfileCoverage, fderiv ℝ f y = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian G f y v v := by
    intro y hy _
    exact hessianMargins_positive_two_plane G f y (hg t y hy)
  obtain ⟨ψ,hψ,hc,hs,hclose,hinside,hncψ,hcritψ,hmass⟩ :=
    exists_global_box_amplified_profile G sourceSignBox
      (sphericalBaseProfile_chart_smooth sourcePole sourceAxisOne sourceAxisTwo t)
      hnc hcrit sourceSignBox_subset_coverage (source_baseProfile_sign_gradient g₀ hg₀ g t) T htol
  let φ := sphericalProfileGlue sourcePole sourceAxisOne sourceAxisTwo t ψ
  have hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ :=
    sphericalProfileGlue_smooth sourcePole sourceAxisOne sourceAxisTwo t hψ hc
  have hchart : φ ∘ (chartAt (Euclidean 3) sourcePole).symm = ψ :=
    sphericalProfileGlue_chart sourcePole sourceAxisOne sourceAxisTwo t ψ
  have hsp : tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆
      sourceSignRegion := sphericalProfileGlue_tsupport sourcePole sourceAxisOne sourceAxisTwo t hc hs
  have hcl := sphericalProfileGlue_close sourcePole sourceAxisOne sourceAxisTwo t htol hclose
  obtain ⟨hin,hout⟩ := henvelope t ht φ hsp (fun q => (hcl q).trans_le (min_le_right _ _))
  refine ⟨φ,hφ,hsp,(fun q => (hcl q).trans_le (min_le_left _ _)),hin,hout,?_,?_,?_,?_⟩
  · simpa only [hchart] using hncψ
  · simpa only [hchart] using hcritψ
  · simpa only [hchart] using hinside
  · simpa only [hchart] using hmass

end YauCounterexamples

end

end OAI
