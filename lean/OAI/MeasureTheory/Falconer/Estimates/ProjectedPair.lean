import OAI.MeasureTheory.Falconer.Measures.ChooseProjectedFrostman
import OAI.MeasureTheory.Falconer.Shells.PositiveRestriction
import OAI.MeasureTheory.Falconer.Geometry.ProjectionDilation

namespace OAI

/-! # Original separated pairs with simultaneous projected Frostman bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure ProjectedStartingPair {d : ℕ} (ζ : ProbabilityMeasure (Space d))
    (m : ℕ) (s ε : ℝ) where
  projection : Space d →L[ℝ] Space m
  left : ProbabilityMeasure (Space d)
  right : ProbabilityMeasure (Space d)
  left_compact : IsCompact (left : Measure (Space d)).support
  right_compact : IsCompact (right : Measure (Space d)).support
  left_ac : (left : Measure (Space d)) ≪ (ζ : Measure (Space d))
  right_ac : (right : Measure (Space d)) ≪ (ζ : Measure (Space d))
  constant : ℝ
  constant_pos : 0 < constant
  left_frostman : FrostmanBallBound (left : Measure (Space d)) s constant
  right_frostman : FrostmanBallBound (right : Measure (Space d)) s constant
  projected_left_frostman : FrostmanBallBound ((left : Measure (Space d)).map projection) s constant
  projected_right_frostman : FrostmanBallBound ((right : Measure (Space d)).map projection) s constant
  contractive : ‖projection‖ ≤ 1
  radius : ℝ
  radius_pos : 0 < radius
  lower : ℝ
  lower_pos : 0 < lower
  direction : Space d
  direction_unit : ‖direction‖ = 1
  geometry : ∀ x ∈ (left : Measure (Space d)).support,
    ∀ y ∈ (right : Measure (Space d)).support,
      radius/2 ≤ dist x y ∧ dist x y ≤ 2*radius ∧
      lower ≤ ‖projection (radialDirection x y)‖ ∧
      lower ≤ ‖projection (radialDirection y x)‖ ∧
      dist (radialDirection x y) direction < ε

variable {d m : ℕ}

private theorem frostman_enlarge {μ : Measure (Space d)} {s C D : ℝ}
    (h : FrostmanBallBound μ s C) (hCD : C ≤ D) : FrostmanBallBound μ s D := by
  intro x r hr
  exact (h x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hr.le _)))

theorem exists_projected_starting_pair (ζ : ProbabilityMeasure (Space d))
    {s C u ε : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (m:ℝ))
    (hfrost : FrostmanBallBound (ζ : Measure (Space d)) s C) (hε : 0 < ε) :
    Nonempty (ProjectedStartingPair ζ m u ε) := by
  obtain ⟨P,μ,hK,hdom,D,hD,hμ,hP⟩ := choose_projected_frostman ζ hu hus hum hfrost
  obtain ⟨a,ha,hcontract⟩ := exists_contractive_dilation P
  let Q := a • P
  have hQ : FrostmanBallBound ((μ : Measure (Space d)).map Q) u (D*a^(-u)) :=
    dilated_projected_frostman (μ : Measure (Space d)) P ha hP
  let := noAtoms_of_frostman ((μ : Measure (Space d)).map Q) hu hQ
  obtain ⟨A,B,hAc,hBc,_,_,hAm,hBm,r,c,hr,hc,w,hw,hgeom⟩ :=
    projected_compact_pieces μ hK Q hε
  let μ₁ := positiveRestriction μ A hAm
  let μ₂ := positiveRestriction μ B hBm
  have hleft : (μ₁ : Measure (Space d)).support ⊆ A :=
    positiveRestriction_support μ A hAm hAc.isClosed
  have hright : (μ₂ : Measure (Space d)).support ⊆ B :=
    positiveRestriction_support μ B hBm hBc.isClosed
  let C₁ := ((μ : Measure (Space d)) A).toReal⁻¹ * D
  let C₂ := ((μ : Measure (Space d)) B).toReal⁻¹ * D
  let C₃ := ((μ : Measure (Space d)) A).toReal⁻¹ * (D*a^(-u))
  let C₄ := ((μ : Measure (Space d)) B).toReal⁻¹ * (D*a^(-u))
  have hC₁ : 0 < C₁ := mul_pos (inv_pos.mpr
    (ENNReal.toReal_pos hAm.ne' (measure_ne_top _ _))) hD
  let C' := max (max C₁ C₂) (max C₃ C₄)
  have h1 : C₁ ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : C₂ ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : C₃ ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have h4 : C₄ ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  have hf1 : FrostmanBallBound (μ₁ : Measure (Space d)) u C₁ := by
    have hb := positiveRestriction_projected_frostman μ A hAm (ContinuousLinearMap.id ℝ (Space d))
      (by simpa using hμ)
    simpa [C₁] using hb
  have hf2 : FrostmanBallBound (μ₂ : Measure (Space d)) u C₂ := by
    have hb := positiveRestriction_projected_frostman μ B hBm (ContinuousLinearMap.id ℝ (Space d))
      (by simpa using hμ)
    simpa [C₂] using hb
  exact ⟨{
    projection := Q
    left := μ₁
    right := μ₂
    left_compact := hAc.of_isClosed_subset Measure.isClosed_support hleft
    right_compact := hBc.of_isClosed_subset Measure.isClosed_support hright
    left_ac := (positiveRestriction_absolutelyContinuous μ A hAm).trans hdom
    right_ac := (positiveRestriction_absolutelyContinuous μ B hBm).trans hdom
    constant := C'
    constant_pos := hC₁.trans_le h1
    left_frostman := frostman_enlarge hf1 h1
    right_frostman := frostman_enlarge hf2 h2
    projected_left_frostman := frostman_enlarge
      (positiveRestriction_projected_frostman μ A hAm Q hQ) h3
    projected_right_frostman := frostman_enlarge
      (positiveRestriction_projected_frostman μ B hBm Q hQ) h4
    contractive := hcontract
    radius := r
    radius_pos := hr
    lower := c
    lower_pos := hc
    direction := w
    direction_unit := hw
    geometry := fun x hx y hy => hgeom x (hleft hx) y (hright hy) }⟩

end Falconer

end OAI
