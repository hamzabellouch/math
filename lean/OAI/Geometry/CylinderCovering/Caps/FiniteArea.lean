import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.SetProjection
import OAI.Geometry.CylinderCovering.Footprints.Area
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite
open TriangularCovering

private def normalFirst : Space := !₂[1, 0, 0]
private def normalSecond : Space := !₂[0, 1, 0]
private def radialFirst : Space := !₂[0, 0, height]
private def radialSecond : Space := !₂[0, 0, -height]
private def transverseFirst : Space := !₂[0, 1/2, 0]
private def transverseSecond : Space := !₂[1/2, 0, 0]
private def originSecond : Space := !₂[0, 0, height]
private def velocityFirst (δ r : ℝ) : Space := !₂[0, δ*alpha r, 2*height*δ*beta r]
private def velocitySecond (δ r : ℝ) : Space := !₂[-δ*alpha r, 0, 2*height*δ*beta r]

private lemma height_positive : 0 < height := by unfold height; positivity
private lemma height_squared : height ^ 2 = 1/2 := by norm_num [height, div_pow]

private lemma normalFirst_unit : ‖normalFirst‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  norm_num [normalFirst, Fin.sum_univ_succ]
private lemma normalSecond_unit : ‖normalSecond‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  norm_num [normalSecond, Fin.sum_univ_succ]

private lemma first_chart :
    (RadialProjection.coordinateAffine 0 radialFirst transverseFirst : (ℝ × ℝ) → Space) = firstFoot := by
  funext p
  ext i
  fin_cases i <;> simp [RadialProjection.coordinateAffine, radialFirst, transverseFirst, firstFoot] <;> ring
private lemma second_chart :
    (RadialProjection.coordinateAffine originSecond radialSecond transverseSecond : (ℝ × ℝ) → Space) = secondFoot := by
  funext p
  ext i
  fin_cases i <;> simp [RadialProjection.coordinateAffine, originSecond, radialSecond, transverseSecond, secondFoot] <;> ring

private lemma first_raw (δ r : ℝ) : normalFirst + velocityFirst δ r = firstRaw δ r := by
  ext i
  fin_cases i <;> simp [normalFirst, velocityFirst, firstRaw]
private lemma second_raw (δ r : ℝ) : normalSecond + velocitySecond δ r = secondRaw δ r := by
  ext i
  fin_cases i <;> simp [normalSecond, velocitySecond, secondRaw]

private lemma first_gram :
    Real.sqrt (inner ℝ radialFirst radialFirst * inner ℝ transverseFirst transverseFirst -
      (inner ℝ radialFirst transverseFirst)^2) = height/2 := by
  have h : inner ℝ radialFirst radialFirst * inner ℝ transverseFirst transverseFirst -
      (inner ℝ radialFirst transverseFirst)^2 = (height/2)^2 := by
    simp only [inner_coord, radialFirst, transverseFirst]
    dsimp
    ring
  rw [h, Real.sqrt_sq (div_nonneg height_positive.le (by norm_num))]
private lemma second_gram :
    Real.sqrt (inner ℝ radialSecond radialSecond * inner ℝ transverseSecond transverseSecond -
      (inner ℝ radialSecond transverseSecond)^2) = height/2 := by
  have h : inner ℝ radialSecond radialSecond * inner ℝ transverseSecond transverseSecond -
      (inner ℝ radialSecond transverseSecond)^2 = (height/2)^2 := by
    simp only [inner_coord, radialSecond, transverseSecond]
    dsimp
    ring
  rw [h, Real.sqrt_sq (div_nonneg height_positive.le (by norm_num))]

private lemma velocityFirst_norm_sq (δ r : ℝ) :
    ‖velocityFirst δ r‖^2 = δ^2*(alpha r^2+2*beta r^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [velocityFirst, Fin.sum_univ_succ]
  nlinarith only [height_squared]
private lemma velocitySecond_norm_sq (δ r : ℝ) :
    ‖velocitySecond δ r‖^2 = δ^2*(alpha r^2+2*beta r^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [velocitySecond, Fin.sum_univ_succ]
  nlinarith only [height_squared]

theorem firstFoot_projection_area (δ r : ℝ) (S : Set (ℝ × ℝ)) :
    area (projection (firstAxis δ r) '' (firstFoot '' S)) =
      (height/2) / Real.sqrt (1+δ^2*(alpha r^2+2*beta r^2)) * volume.real S := by
  have h := RadialProjection.radial_affine_projection_area 0 normalFirst radialFirst transverseFirst
    (velocityFirst δ r) normalFirst_unit
    (by simp [inner_coord, normalFirst, radialFirst])
    (by simp [inner_coord, normalFirst, transverseFirst])
    (by simp [inner_coord, normalFirst, velocityFirst]) S
  rw [first_chart, first_raw, first_gram, velocityFirst_norm_sq] at h
  exact h

theorem secondFoot_projection_area (δ r : ℝ) (S : Set (ℝ × ℝ)) :
    area (projection (secondAxis δ r) '' (secondFoot '' S)) =
      (height/2) / Real.sqrt (1+δ^2*(alpha r^2+2*beta r^2)) * volume.real S := by
  have h := RadialProjection.radial_affine_projection_area originSecond normalSecond radialSecond transverseSecond
    (velocitySecond δ r) normalSecond_unit
    (by simp [inner_coord, normalSecond, radialSecond])
    (by simp [inner_coord, normalSecond, transverseSecond])
    (by simp [inner_coord, normalSecond, velocitySecond]) S
  rw [second_chart, second_raw, second_gram, velocitySecond_norm_sq] at h
  exact h

theorem firstFoot_projection_finite (δ r : ℝ) {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    Measure.euclideanHausdorffMeasure 2
      (projection (firstAxis δ r) '' (firstFoot '' S)) ≠ ⊤ := by
  have hp : inner ℝ normalFirst (velocityFirst δ r) = 0 := by
    simp [inner_coord, normalFirst, velocityFirst]
  have h := RadialProjection.affine_projection_finite 0
    (unit (normalFirst + velocityFirst δ r)) radialFirst transverseFirst
    (unit_norm (RadialProjection.sideways_ne_zero normalFirst_unit hp)) hS
  rw [first_chart, first_raw] at h
  exact h

theorem secondFoot_projection_finite (δ r : ℝ) {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    Measure.euclideanHausdorffMeasure 2
      (projection (secondAxis δ r) '' (secondFoot '' S)) ≠ ⊤ := by
  have hp : inner ℝ normalSecond (velocitySecond δ r) = 0 := by
    simp [inner_coord, normalSecond, velocitySecond]
  have h := RadialProjection.affine_projection_finite originSecond
    (unit (normalSecond + velocitySecond δ r)) radialSecond transverseSecond
    (unit_norm (RadialProjection.sideways_ne_zero normalSecond_unit hp)) hS
  rw [second_chart, second_raw] at h
  exact h

theorem firstBase_area {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1) 1)) (hR0 : ∀ r ∈ Icc (-1) 1, 0 ≤ R r)
    (N : ℕ) (i : Fin N) : area (firstBase δ R N i) = localArea δ R N i := by
  have hM : 0 ≤ maxCap R N i := RadialRiemann.capMax_nonneg (by norm_num) hR hR0 i
  have hρ : 0 ≤ halfwidth N := by unfold halfwidth; positivity
  have he : 0 ≤ collar δ N := by unfold collar; positivity
  rw [firstBase, firstFoot_projection_area, foot, RadialFootprints.halfheightFootprint_area _ hρ he hM]
  unfold localArea
  ring

theorem secondBase_area {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1) 1)) (hR0 : ∀ r ∈ Icc (-1) 1, 0 ≤ R r)
    (N : ℕ) (i : Fin N) : area (secondBase δ R N i) = localArea δ R N i := by
  have hM : 0 ≤ maxCap R N i := RadialRiemann.capMax_nonneg (by norm_num) hR hR0 i
  have hρ : 0 ≤ halfwidth N := by unfold halfwidth; positivity
  have he : 0 ≤ collar δ N := by unfold collar; positivity
  rw [secondBase, secondFoot_projection_area, foot, RadialFootprints.halfheightFootprint_area _ hρ he hM]
  unfold localArea
  ring

theorem totalArea_eq_two_sum {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1) 1)) (hR0 : ∀ r ∈ Icc (-1) 1, 0 ≤ R r)
    (N : ℕ) : totalArea δ R N = 2 * ∑ i : Fin N, localArea δ R N i := by
  unfold totalArea
  simp_rw [firstBase_area hδ hR hR0, secondBase_area hδ hR hR0]
  ring

end CylinderCovering.HalfheightFinite

end

end OAI
