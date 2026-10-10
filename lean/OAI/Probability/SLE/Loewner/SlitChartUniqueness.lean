import OAI.Probability.SLE.Loewner.SlitChartDisplacement

namespace OAI

/-! The normalized static slit chart and its capacity do not depend on a choice. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.unique_on_domain {p : C(unitInterval,ℂ)}
    (P Q : SimpleSlitChart p) :
    EqOn P.forward Q.forward (upperHalfPlane \ range p) ∧
      EqOn P.inverse Q.inverse upperHalfPlane ∧ P.capacity=Q.capacity := by
  have hc : P.capacity=Q.capacity := le_antisymm
    (P.capacity_le_of_range_subset Q Subset.rfl)
    (Q.capacity_le_of_range_subset P Subset.rfl)
  have hcomp (z : ℂ) (hz : z∈upperHalfPlane) : P.forward (Q.inverse z)=z := by
    have hb := P.inverse_comparison Q Subset.rfl hz
    rw [hc,sub_self,zero_div] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  have hi : EqOn P.inverse Q.inverse upperHalfPlane := by
    intro z hz
    have hh := P.left_inverse (Q.inverse z) (Q.inverse_mapsTo hz)
    rw [hcomp z hz] at hh
    exact hh
  refine ⟨?_,hi,hc⟩
  intro z hz
  apply Q.inverse_injOn (P.bijOn.mapsTo hz) (Q.bijOn.mapsTo hz)
  rw [← hi (P.bijOn.mapsTo hz),P.left_inverse z hz,Q.left_inverse z hz]

end SLEExactGauge

end

end OAI
