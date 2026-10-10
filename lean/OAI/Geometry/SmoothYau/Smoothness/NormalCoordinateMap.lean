import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

def normalCoordinateMap (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  normalWaveEquiv.symm (normalJetMap q.1 q.2
    ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv x))

lemma contDiff_normalCoordinateMap (g : SmoothMetric NormalWaveSpace NormalWaveSpace) :
    ContDiff ℝ ∞ (fun w : NormalWaveParameter × (Fin 3 → ℝ) => normalCoordinateMap g w.1 w.2) :=
  normalWaveEquiv.symm.contDiff.comp ((contDiff_normalJetFamily g).comp
    (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)))

lemma normalCoordinateMap_derivative_bound
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ M ≥ 1, ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1 →
      max 1 (3*‖fderiv ℝ (normalCoordinateMap g q) x‖) ≤ M := by
  let F := fun w : NormalWaveParameter × (Fin 3 → ℝ) => normalCoordinateMap g w.1 w.2
  have hF : ContDiff ℝ ∞ F := contDiff_normalCoordinateMap g
  obtain ⟨C,hC⟩ := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall (0 : Fin 3 → ℝ) 1)).exists_bound_of_continuousOn
      ((continuous_parameter_iteratedFDeriv F hF 1).continuousOn)
  refine ⟨max 1 (3*C),le_max_left _ _,?_⟩
  intro q hq x hx
  have hb := hC (q,x) ⟨hq,by simpa [Metric.mem_closedBall,dist_zero_right] using hx⟩
  rw [norm_iteratedFDeriv_one] at hb
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left hb (by norm_num))

end YauCounterexamples
end

end OAI
