import OAI.Analysis.HenonEmden.PressureMismatch

namespace OAI

section DirectionalPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerPressure

lemma IsSolution_directional_pressure {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (weight volume κ e) u q B+
      ENNReal.ofReal (1/(p+1))*weightedEnergyN (weight volume κ e) v p A ≤
      capPressureIntegral (source u q B) (source v p A) κ e+
      capMismatchIntegral (source u q B) (source v p A) κ e+
      2*(lossIntegral u (source u q B) κ δ e+lossIntegral v (source v p A) κ δ e)+
      (ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) u q B+
      ENNReal.ofReal (endpointConstant p A*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) v p A) := by
  apply pressure_cancellation
    (ENNReal.add_ne_top.mpr ⟨IsSolution_endpointIntegral_finite (by omega) h hq hκ hκ1 hδ e,
      IsSolution_endpointIntegral_finite (by omega) h.swap hp hκ hκ1 hδ e⟩)
    (IsSolution_pressure_comparison hn h hp hq hκ hκ1 hδ e) _
    (IsSolution_pairMismatch_bound hn h hp hq hκ hκ1 e)
  have hf := IsSolution_integrated_pressure_recovery (by omega : 2 ≤ n) h hq hκ hκ1 hδ e
  have hg := IsSolution_integrated_pressure_recovery (by omega : 2 ≤ n) h.swap hp hκ hκ1 hδ e
  convert add_le_add hf hg using 1 <;> first | rfl | ac_rfl

end HenonLaneEmden.SpatialComponents
end
end DirectionalPressure

end OAI
