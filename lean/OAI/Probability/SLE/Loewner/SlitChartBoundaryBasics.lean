import OAI.Probability.SLE.Loewner.SlitBoundaryBarrier
import OAI.Probability.SLE.Loewner.InverseBoundaryBound

namespace OAI

/-! Analytic and compactness facts for the actual normalized static slit charts. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.isOpen_domain {p : C(unitInterval,ℂ)} (_P : SimpleSlitChart p) :
    IsOpen (upperHalfPlane \ range p) :=
  isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed

lemma SimpleSlitChart.inverse_injOn {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p) :
    InjOn P.inverse upperHalfPlane := by
  intro z hz w hw he
  have hh := congrArg P.forward he
  simpa only [P.right_inverse z hz,P.right_inverse w hw] using hh

lemma SimpleSlitChart.inverse_im_ge {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {z : ℂ} (hz : z∈upperHalfPlane) : z.im≤(P.inverse z).im := by
  have hh := P.height_le (P.inverse z) (P.inverse_mapsTo hz)
  simpa only [P.right_inverse z hz] using hh

lemma SimpleSlitChart.inverse_bounded_over_ball {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (R : ℝ) :
    ∃ M : ℝ, ∀ w∈upperHalfPlane, ‖w‖≤R → ‖P.inverse w‖≤M :=
  inverse_bound_of_hydrodynamic P.inverse_mapsTo P.right_inverse
    (P.coefficient.mono_left inf_le_left) R

end SLEExactGauge

end

end OAI
