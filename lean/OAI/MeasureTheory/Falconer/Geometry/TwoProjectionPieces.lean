import OAI.MeasureTheory.Falconer.Geometry.TwoProjectionFrame
import OAI.MeasureTheory.Falconer.Shells.PositiveRestriction

namespace OAI

/-! # Positive compact pieces in the normalized two-projection frame -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure TwoProjectionPieces {d m k : ℕ} {μ : ProbabilityMeasure (Space d)}
    {s : ℝ} (f : TwoProjectionFrame μ m k s) (ε : ℝ) where
  leftSet : Set (Space d)
  rightSet : Set (Space d)
  left_compact : IsCompact leftSet
  right_compact : IsCompact rightSet
  left_subset : leftSet ⊆ (μ : Measure (Space d)).support
  right_subset : rightSet ⊆ (μ : Measure (Space d)).support
  left_pos : 0 < (μ : Measure (Space d)) leftSet
  right_pos : 0 < (μ : Measure (Space d)) rightSet
  radius : ℝ
  radius_pos : 0 < radius
  lower : ℝ
  lower_pos : 0 < lower
  direction : Space d
  direction_unit : ‖direction‖ = 1
  geometry : ∀ x ∈ leftSet, ∀ y ∈ rightSet,
    radius/2 ≤ dist x y ∧ dist x y ≤ 2*radius ∧
    lower ≤ ‖(f.second.comp f.first) (radialDirection x y)‖ ∧
    lower ≤ ‖(f.second.comp f.first) (radialDirection y x)‖ ∧
    dist (radialDirection x y) direction < ε

variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}

theorem exists_two_projection_pieces (hK : IsCompact (μ : Measure (Space d)).support)
    (f : TwoProjectionFrame μ m k s) (hs : 0 < s) (hε : 0 < ε) :
    Nonempty (TwoProjectionPieces f ε) := by
  let := noAtoms_of_frostman ((μ : Measure (Space d)).map (f.second.comp f.first)) hs f.second_frostman
  obtain ⟨A,B,hA,hB,hAs,hBs,hAp,hBp,r,c,hr,hc,w,hw,hgeom⟩ :=
    projected_compact_pieces μ hK (f.second.comp f.first) hε
  exact ⟨⟨A,B,hA,hB,hAs,hBs,hAp,hBp,r,hr,c,hc,w,hw,hgeom⟩⟩

namespace TwoProjectionPieces
variable {f : TwoProjectionFrame μ m k s} (p : TwoProjectionPieces f ε)

noncomputable def left : ProbabilityMeasure (Space d) :=
  positiveRestriction μ p.leftSet p.left_pos

noncomputable def right : ProbabilityMeasure (Space d) :=
  positiveRestriction μ p.rightSet p.right_pos

theorem left_support : (p.left : Measure (Space d)).support ⊆ p.leftSet :=
  positiveRestriction_support μ p.leftSet p.left_pos p.left_compact.isClosed

theorem right_support : (p.right : Measure (Space d)).support ⊆ p.rightSet :=
  positiveRestriction_support μ p.rightSet p.right_pos p.right_compact.isClosed

theorem left_support_compact : IsCompact (p.left : Measure (Space d)).support :=
  p.left_compact.of_isClosed_subset Measure.isClosed_support p.left_support

theorem right_support_compact : IsCompact (p.right : Measure (Space d)).support :=
  p.right_compact.of_isClosed_subset Measure.isClosed_support p.right_support

theorem left_ac : (p.left : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
  positiveRestriction_absolutelyContinuous μ p.leftSet p.left_pos

theorem right_ac : (p.right : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
  positiveRestriction_absolutelyContinuous μ p.rightSet p.right_pos

theorem first_lower {x y : Space d} (hx : x ∈ p.leftSet) (hy : y ∈ p.rightSet) :
    p.lower ≤ ‖f.first (radialDirection x y)‖ ∧
    p.lower ≤ ‖f.first (radialDirection y x)‖ := by
  have hbound (v : Space d) : ‖(f.second.comp f.first) v‖ ≤ ‖f.first v‖ :=
    (f.second.le_opNorm (f.first v)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right f.second_contractive (norm_nonneg (f.first v)))
  exact ⟨(p.geometry x hx y hy).2.2.1 |>.trans (hbound _),
    (p.geometry x hx y hy).2.2.2.1 |>.trans (hbound _)⟩

noncomputable def constant : ℝ :=
  max (((μ : Measure (Space d)) p.leftSet).toReal⁻¹)
    (((μ : Measure (Space d)) p.rightSet).toReal⁻¹) * f.constant

theorem constant_pos : 0 < p.constant := by
  apply mul_pos _ f.constant_pos
  exact (inv_pos.mpr (ENNReal.toReal_pos p.left_pos.ne' (measure_ne_top _ _))).trans_le (le_max_left _ _)

theorem projected_frostman {q : ℕ} (P : Space d →L[ℝ] Space q)
    (h : FrostmanBallBound ((μ : Measure (Space d)).map P) s f.constant) :
    FrostmanBallBound ((p.left : Measure (Space d)).map P) s p.constant ∧
    FrostmanBallBound ((p.right : Measure (Space d)).map P) s p.constant := by
  constructor
  · intro x r hr
    apply (positiveRestriction_projected_frostman μ p.leftSet p.left_pos P h x r hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) f.constant_pos.le
  · intro x r hr
    apply (positiveRestriction_projected_frostman μ p.rightSet p.right_pos P h x r hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) f.constant_pos.le

end TwoProjectionPieces
end Falconer

end OAI
