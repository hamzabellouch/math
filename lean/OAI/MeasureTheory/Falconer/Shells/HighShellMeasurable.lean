import OAI.MeasureTheory.Falconer.Shells.HighShellOrderForm

namespace OAI

namespace PlanarFalconer
open MeasureTheory
namespace PositiveDistanceData

theorem normalizedHighShellF_measurable (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (n : ℕ) (v : ℝ) :
    Measurable (d.normalizedHighShellF n v) := by
  have he (r : ℝ) : d.normalizedHighShellF n v r =
      (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ) *
        ∑ j ∈ Finset.range (n+1), ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ)*d.inverseOrderForm j v r :=
    d.normalizedHighShellF_finite_separation hQ hs n v r
  simp_rw [show d.normalizedHighShellF n v = _ from funext he]
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_sum
    intro j hj
    exact (by fun_prop : Measurable (fun r : ℝ => ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ))).mul
      (d.inverseOrderForm_data hQ j v).1

end PositiveDistanceData

end PlanarFalconer

end OAI
