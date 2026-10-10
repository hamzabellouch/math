import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRowRestriction
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingBinShift

namespace OAI

/-! The literal stopped beta on a dilated norm envelope is the existing
analytic row after the exact shift of descending geometric bin labels.
The cutoff parameters and every selected-side condition remain unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_geometric_eq_row {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z Z Q : ℝ)
    (j k h : ℕ) (early : Bool) {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
        (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) b =
      stoppedRowCoefficient X w z 0 W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h Z Q early) b := by
  rw [stoppedBeta_eq_stoppedRowCoefficient hXF W w z _ hb hbX]
  unfold stoppedRowCoefficient
  congr 1
  apply stoppedBeta_selected_congr
  intro r _ d hd _
  have hdp := mem_primaryElementBall.mp hd
  exact geometricStoppedSideTest_shift hρ hX hXF hdp.1 hdp.2 j k h Z Q early r

end CubicFirstMoment

end

end OAI
