import OAI.Analysis.LipschitzHilbert.Estimates.CompactCompositionCommutator
import OAI.Analysis.LipschitzHilbert.Geometry.SmoothDirectionApproximation
import OAI.Analysis.LipschitzHilbert.Fourier.LineCompositionLimit

namespace OAI

/-! The composition commutator for the actual bounded Lipschitz
directions, obtained from compact smooth approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lipschitzCompositionCommutator_L2 (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hub : ∀ y, |u y|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t f)-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) f)‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f‖ := by
  let v := fun n => (smoothDirectionApprox u hu hub n : ℝ → ℝ)
  have hv (n : ℕ) : LipschitzWith 1 (v n) := smoothDirectionApprox_lipschitz u hu hub n
  have hvb (n : ℕ) (y : ℝ) : |v n y|≤1 := smoothDirectionApprox_bound u hu hub n y
  have hvl (y : ℝ) : Tendsto (fun n => v n y) atTop (𝓝 (u y)) :=
    smoothDirectionApprox_tendsto u hu hub y
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  have hc1 := lineSamplingL2Path_tendsto v u hv hu hvb hub hvl t ht' f
  have hc2 := lineSamplingL2Path_tendsto v u hv hu hvb hub hvl t ht'
    (lineL2Projection m 1 (by norm_num) f)
  have hlim := (((lineL2Projection m 1 (by norm_num)).continuous.continuousAt.tendsto.comp hc1).sub hc2).norm
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n => compactCompositionCommutator_L2 (v n) (hv n)
    ((smoothDirectionApprox u hu hub n).smooth ⊤) (smoothDirectionApprox_compact u hu hub n)
    1 (by norm_num) (hvb n) m A hA hm t ht f

end LipschitzHilbert.PacketRepresentation

end

end OAI
