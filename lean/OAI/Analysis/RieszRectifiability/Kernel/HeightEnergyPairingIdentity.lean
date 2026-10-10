import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.RenormalizedFractionalHeightIdentity
import OAI.Analysis.RieszRectifiability.Kernel.ComplexInteriorEnergy

namespace OAI

/-!
# Height-energy pairing for compactly supported Schwartz tests

Finite interior fractional energy and a weighted exterior height bound give
integrability of the fractional Schwartz pairing and identify it with the
renormalized complex height pairing on the ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric SchwartzMap

theorem compact_schwartz_height_energy_pairing_identity (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume)
    (henergy : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R)))) :
    Integrable (fun x => w x • fractionalSchwartzTest p g x) volume ∧
      (∫ x, w x • fractionalSchwartzTest p g x) =
        complexHeightPairingOn (p + 1) volume a (ball a R) w g := by
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  let ν := (volume : Measure (Ambient (p + 1))).restrict (ball a R)
  have hgrowth : GlobalUpperGrowth (p + 1) C (volume : Measure (Ambient (p + 1))) :=
    volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C volume hgrowth a R hR
  have hI := complex_height_interior_integrable_of_energy p C ν
    (globalGrowth_restrict (p + 1) C volume hgrowth (ball a R)) w hwm hw g henergy
  have hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume :=
    polynomial_weight_integrable_from_height_tail (p + 3) volume w hwm a R hR hw hweighted
  refine ⟨(height_fractional_test_integrable_and_bound p volume w hwm hweight g hzero).1, ?_⟩
  exact compact_schwartz_renormalized_height_identity p a H R hH hR hHR w hwm hw
    hweight g hzero hnear (SchwartzMap.seminorm ℝ 0 0 g)
    (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) g) (g.norm_le_seminorm ℝ) hweighted hI

end

end RieszRectifiability

end OAI
