import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import OAI.Geometry.NodalSets.Elliptic.RealCompactH1Approximation

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

theorem real_L2_pointwise_limit_ae {n : ℕ} (w : ℕ → Coord n → ℝ)
    (hw : ∀ j, MemLp (w j) 2 volume) (u v : Coord n → ℝ)
    (hu : MemLp u 2 volume)
    (hl : Tendsto (fun j ↦ (hw j).toLp (w j)) atTop (𝓝 (hu.toLp u)))
    (hp : ∀ x, Tendsto (fun j ↦ w j x) atTop (𝓝 (v x))) :
    v =ᵐ[volume] u := by
  have hm := (tendstoInMeasure_of_tendsto_Lp hl).congr
    (fun j ↦ (hw j).coeFn_toLp) hu.coeFn_toLp
  obtain ⟨nu,hnu,ha⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [ha] with x hx
  exact tendsto_nhds_unique ((hp x).comp hnu.tendsto_atTop) hx

end
end Yau

end OAI
