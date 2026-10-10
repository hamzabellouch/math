import OAI.Analysis.CoulombTransport.LocalCertificate
import OAI.Analysis.CoulombTransport.StationaryMap

namespace OAI

universe uE

noncomputable section

open Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.LocalGeometry

open StationaryMap CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem statePotential_center_value {a : E} (ha : ‖a‖ = 1) :
    statePotential a a (0, -a) = 0 := by
  have hvec : -a - a = (-2 : ℝ) • a := by module
  have hnorm : ‖-a - a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  simp [statePotential, pairCost, ha, hnorm]
  norm_num

/-- The branch value vanishes at the center, as required to glue the five
local potentials with values `5/2,0,0,0,0`. -/
theorem localSupporting_value_center {a : E} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    C.value a = 0 := by
  rw [C.value_base]
  exact statePotential_center_value ha

/-- Restore the central and opposite quadratic potentials in the local
supporting inequality. This is the literal three-point Coulomb formula. -/
theorem local_coulomb_supporting {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2) ≤
      ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.supporting y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y] at h
  linarith

/-- Equality in the supporting inequality is exactly the stationary branch,
not merely inclusion of the branch in the contact set. -/
theorem local_coulomb_contact {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    (‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ =
      ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.contact y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y, Prod.mk.injEq] at h
  rw [← h]
  constructor <;> intro heq <;> linarith

end Problem356.LocalGeometry

end

end OAI
