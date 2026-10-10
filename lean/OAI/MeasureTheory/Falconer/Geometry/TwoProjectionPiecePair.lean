import OAI.MeasureTheory.Falconer.Geometry.TwoProjectionPieces
import OAI.MeasureTheory.Falconer.Estimates.ProjectedPair
import OAI.MeasureTheory.Falconer.Angular.DirectionDistance

namespace OAI

/-! # The first auxiliary pair and its inherited root geometry -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}
  {f : TwoProjectionFrame μ m k s}

namespace TwoProjectionPieces
variable (p : TwoProjectionPieces f ε)

noncomputable def firstPair : ProjectedStartingPair μ m s ε := by
  have horig := p.projected_frostman (ContinuousLinearMap.id ℝ (Space d))
    (by simpa using f.original_frostman)
  have hfirst := p.projected_frostman f.first f.first_frostman
  refine {
    projection := f.first
    left := p.left
    right := p.right
    left_compact := p.left_support_compact
    right_compact := p.right_support_compact
    left_ac := p.left_ac
    right_ac := p.right_ac
    constant := p.constant
    constant_pos := p.constant_pos
    left_frostman := by simpa using horig.1
    right_frostman := by simpa using horig.2
    projected_left_frostman := hfirst.1
    projected_right_frostman := hfirst.2
    contractive := f.first_contractive
    radius := p.radius
    radius_pos := p.radius_pos
    lower := p.lower
    lower_pos := p.lower_pos
    direction := p.direction
    direction_unit := p.direction_unit
    geometry := ?_ }
  intro x hx y hy
  have hx' := p.left_support hx
  have hy' := p.right_support hy
  obtain ⟨h1,h2,_,_,h5⟩ := p.geometry x hx' y hy'
  obtain ⟨h3,h4⟩ := p.first_lower hx' hy'
  exact ⟨h1,h2,h3,h4,h5⟩

theorem first_support_left :
    ((p.left : Measure (Space d)).map f.first).support ⊆ (centeredUnitCube m).carrier := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  exact f.first_root y (p.left_subset (p.left_support hy))

theorem first_support_right :
    ((p.right : Measure (Space d)).map f.first).support ⊆ (centeredUnitCube m).carrier := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hx
  exact f.first_root y (p.right_subset (p.right_support hy))

theorem first_noncharging (w : Space m) (hw : ‖w‖ = 1) (t : ℝ) :
    (((p.left : Measure (Space d)).map f.first)+
      ((p.right : Measure (Space d)).map f.first)) {y | inner ℝ w y = t} = 0 := by
  rw [Measure.add_apply]
  have hL := (p.left_ac.map f.first.continuous.measurable) (f.noncharging w hw t)
  have hR := (p.right_ac.map f.first.continuous.measurable) (f.noncharging w hw t)
  rw [hL,hR,add_zero]

theorem first_pair_separation :
    ∀ x ∈ ((p.left : Measure (Space d)).map f.first).support,
    ∀ y ∈ ((p.right : Measure (Space d)).map f.first).support,
      p.lower*(p.radius/2) ≤ dist x y := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  obtain ⟨b,hb,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hy
  exact projected_distance_lower f.first a b p.lower_pos.le (by linarith [p.radius_pos])
    (p.geometry a (p.left_support ha) b (p.right_support hb)).1
    (p.first_lower (p.left_support ha) (p.right_support hb)).1

theorem second_direction_lower :
    ∀ x ∈ ((p.left : Measure (Space d)).map f.first).support,
    ∀ y ∈ ((p.right : Measure (Space d)).map f.first).support,
      p.lower/4 ≤ ‖f.second (radialDirection x y)‖ ∧
      p.lower/4 ≤ ‖f.second (radialDirection y x)‖ := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  obtain ⟨b,hb,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hy
  obtain ⟨hlo,hhi,h1,h2,_⟩ := p.geometry a (p.left_support ha) b (p.right_support hb)
  have hdist := (contractive_distance_le f.first f.first_contractive a b).trans hhi
  have hlower := projected_distance_lower (f.second.comp f.first) a b p.lower_pos.le
    (by linarith [p.radius_pos]) hlo h1
  have hradius : 0 < p.lower*(p.radius/2) := mul_pos p.lower_pos (by linarith [p.radius_pos])
  have heq : (p.lower*(p.radius/2))/(2*p.radius) = p.lower/4 := by
    field_simp [p.radius_pos.ne']
    ring
  constructor
  · rw [← heq]
    exact projected_direction_lower_of_dist f.second (f.first a) (f.first b) hradius hlower hdist
  · rw [← heq]
    apply projected_direction_lower_of_dist f.second (f.first b) (f.first a) hradius
    · simpa only [ContinuousLinearMap.comp_apply,dist_comm] using hlower
    · simpa only [dist_comm] using hdist

end TwoProjectionPieces
end Falconer

end OAI
