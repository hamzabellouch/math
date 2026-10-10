import OAI.Analysis.IrrationalRotation.Rotation.CircleTailAttenuation
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionRatios

namespace OAI

noncomputable section
open MeasureTheory Set Function
namespace Invariant233.CircleCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_point_finite_floor_support (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ, HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 (point p hr side ω) + (k : ℝ) * p.alpha θ i.2)) := by
  have h := CircleWeights.ae_all_int_finite_floor_support_of_map_ac (law p j)
    θ p.coordFrequency hp.coordFrequency_ne_zero hp.summable_coord_phases
    (point p hr side) (measurable_point hp hr side).aemeasurable
    (endpoint_absolutelyContinuous hp j hr side)
  simpa only [p.coord_coordinate_eq, p.coord_phase_eq] using h

lemma ae_point_cocycle_antitone (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, Antitone (fun k : ℤ => p.floorCocycle θ k (point p hr side ω)) :=
  (ae_point_finite_floor_support hp j hr side).mono
    (fun _ h => hp.parameter_cocycle_antitone _ h)

lemma ae_cocycle_two_ratio_bounds (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ n : ℕ, ∀ v : ℤ,
      0 < p.floorCocycle θ ((n : ℤ) + v) (point p hr true ω) /
        p.floorCocycle θ v (point p hr false ω) ∧
      p.floorCocycle θ ((n : ℤ) + v) (point p hr true ω) /
        p.floorCocycle θ v (point p hr false ω) ≤
        min (p.floorCocycle θ v (point p hr true ω) /
          p.floorCocycle θ v (point p hr false ω))
          (p.floorCocycle θ ((n : ℤ) + v) (point p hr true ω) /
            p.floorCocycle θ ((n : ℤ) + v) (point p hr false ω)) ∧
      min (p.floorCocycle θ v (point p hr true ω) /
          p.floorCocycle θ v (point p hr false ω))
          (p.floorCocycle θ ((n : ℤ) + v) (point p hr true ω) /
            p.floorCocycle θ ((n : ℤ) + v) (point p hr false ω)) ≤ 1 := by
  have hratio := hp.ae_parameter_ratio_bounds_of_map_ac (law p j)
    (point p hr false) (point p hr true) (measurable_point hp hr false).aemeasurable
    (measurable_point hp hr true).aemeasurable (endpoint_absolutelyContinuous hp j hr false)
    (endpoint_absolutelyContinuous hp j hr true)
    ((ae_coordinates_ordered hp j hr).mono (fun _ h i => h i.2))
  filter_upwards [ae_point_cocycle_antitone hp j hr false,
    ae_point_cocycle_antitone hp j hr true, hratio] with ω hx hy hxy
  intro n v
  exact InvariantProjection.cocycle_two_ratio_bounds _ _
    (fun k => p.floorCocycle_pos θ k _) (fun k => p.floorCocycle_pos θ k _)
    hx hy (fun k => (hxy k).1) n v

end Invariant233.CircleCoupling

end

end OAI
