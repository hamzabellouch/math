import OAI.MeasureTheory.Falconer.Geometry.SelectedChartRelation
import OAI.MeasureTheory.Falconer.Angular.CappedOriginalCover

namespace OAI

/-! # Geometry of the retained relation on the original chart labels -/

namespace Falconer
open Set
open scoped ENNReal
variable {n h : ℕ} {ι : Type*}

theorem selectedChartRelation_point_bound
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) (R T : ℝ) {D : ℝ}
    (hE : ∀ u ∈ E, ‖u.1‖ ≤ D) :
    ∀ u ∈ selectedChartRelation A z δ E J v R T, ‖u.1‖ ≤ D := by
  intro u hu
  exact hE (u.1,gnomonicChart u.2) hu.1.1.1

theorem selectedChartRelation_kernel_band
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) (R T : ℝ)
    (hprojection : ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) :
    ∀ u ∈ selectedChartRelation A z δ E J v R T,
      gnomonicChart u.2 ∈ directionSliceBand (gaussianRowMap A).ker (2*(h:ℝ)*δ) := by
  intro u hu
  have hw : gnomonicChart u.2 ∈ gaussianDirectionBand A δ := hu.1.2.2
  have hh := gaussian_direction_band_kernel_distance A (by norm_num) hprojection hw
  change ‖(gaussianRowMap A).kerᗮ.starProjection (gnomonicChart u.2 : Space (n+1))‖ ≤ 2*(h:ℝ)*δ
  convert hh using 1
  ring

theorem selectedChartRelation_original_cover
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) {C M T D : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hA : ∀ i, ‖A i‖ ≤ M) (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space (n+1)) (u.1-v i)‖ ≤ C*δ) :
    ∀ u ∈ selectedChartRelation A z δ E J v (δ+(2*D)*δ+(C*δ)*M) T,
      ∃ c ∈ (cappedActiveAnchors A z (J (gnomonicChart u.2)) v (δ+(2*D)*δ+(C*δ)*M) T).image v,
        ‖perpendicularPart (gnomonicChart u.2 : Space (n+1)) (u.1-c)‖ ≤ C*δ := by
  intro u hu
  exact gaussian_capped_original_cover A z E J v hM hT hA hbounded hanchor hcover
    hu.1.2.1 hu.1.2.2 hu.1.1

end Falconer

end OAI
