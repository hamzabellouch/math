import OAI.Probability.SLE.Loewner.SlitChartUniqueness

namespace OAI

/-! Normalized charts depend only on the slit range, including when its
parameter has been changed. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.eq_of_range_eq {p q : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (Q : SimpleSlitChart q) (hr : range p=range q) :
    P.capacity=Q.capacity ∧ EqOn P.inverse Q.inverse upperHalfPlane ∧
      EqOn P.forward Q.forward (upperHalfPlane \ range p) := by
  have hc : P.capacity=Q.capacity := le_antisymm
    (P.capacity_le_of_range_subset Q hr.le) (Q.capacity_le_of_range_subset P hr.ge)
  have hcomp (z : ℂ) (hz : z∈upperHalfPlane) : P.forward (Q.inverse z)=z := by
    have hb := P.inverse_comparison Q hr.le hz
    rw [hc,sub_self,zero_div] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  have hi : EqOn P.inverse Q.inverse upperHalfPlane := by
    intro z hz
    have hh := P.left_inverse (Q.inverse z) (by simpa only [hr] using Q.inverse_mapsTo hz)
    rw [hcomp z hz] at hh
    exact hh
  refine ⟨hc,hi,?_⟩
  intro z hz
  have hzQ : z∈upperHalfPlane \ range q := by simpa only [hr] using hz
  apply Q.inverse_injOn (P.bijOn.mapsTo hz) (Q.bijOn.mapsTo hzQ)
  rw [← hi (P.bijOn.mapsTo hz),P.left_inverse z hz,Q.left_inverse z hzQ]

end SLEExactGauge

end

end OAI
