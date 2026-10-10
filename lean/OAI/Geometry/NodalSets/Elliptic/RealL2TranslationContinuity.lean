import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceQuotient

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem realL2Translate_continuous {n : ℕ} (u : RealEuclideanL2 n) :
    Continuous (fun v : (Fin n → ℝ) ↦ realL2Translate v u) := by
  let shift : (Fin n → ℝ) → C((Fin n → ℝ),(Fin n → ℝ)) := fun v ↦ ⟨fun x ↦ x+v,continuous_id.add continuous_const⟩
  have hc : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry shift
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hc
    (fun v ↦ measurePreserving_add_right volume v) (by norm_num : (2:ENNReal) ≠ ⊤)

theorem realL2Translate_zero {n : ℕ} (u : RealEuclideanL2 n) : realL2Translate 0 u=u := by
  apply Lp.ext
  filter_upwards [realL2Translate_ae (0 : (Fin n → ℝ)) u] with x hx
  simpa only [add_zero] using hx

theorem realL2Translate_tendsto_zero {n : ℕ} (u : RealEuclideanL2 n) :
    Tendsto (fun v : (Fin n → ℝ) ↦ realL2Translate v u) (𝓝 0) (𝓝 u) := by
  simpa only [realL2Translate_zero] using (realL2Translate_continuous u).continuousAt.tendsto (x := 0)

end
end Yau

end OAI
