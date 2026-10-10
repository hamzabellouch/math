import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SphericalBaseProfileRadius

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local instance chartExtDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartExtDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartExtFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartExtFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def euclideanMetricForm : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

theorem exists_compact_chart_metric_extension (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ (chartAt E p).target) :
    ∃ ĝ : SmoothMetric E E, ∀ᶠ y in 𝓝ˢ K, ∀ v w : E,
      ĝ.inner y v w = g.inner ((chartAt E p).symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y w) := by
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed (chartAt E p).open_target hKO
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E)) (n := ⊤) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV)
  have hη : ContDiff ℝ ∞ η := contMDiff_iff_contDiff.mp η.contMDiff
  have hsη : tsupport η ⊆ (chartAt E p).target := by
    apply (closure_mono (show Function.support η ⊆ V from ?_)).trans hVO
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  have hηφ : ContDiff ℝ ∞ (fun y => η y • chartMetricForm g p y) := by
    rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro y hy
    have hyO := hsη (tsupport_smul_subset_left η (chartMetricForm g p) hy)
    rw [contMDiffAt_iff_contDiffAt]
    exact hη.contDiffAt.smul (((chartMetricForm_contDiffOn g p) y hyO).contDiffAt
      ((chartAt E p).open_target.mem_nhds hyO))
  let B : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y => η y • chartMetricForm g p y + (1-η y) • (euclideanMetricForm (E := E))
  have hB : ContDiff ℝ ∞ B := hηφ.add ((contDiff_const.sub hη).smul contDiff_const)
  have hsym : ∀ y v w, B y v w = B y w v := by
    intro y v w
    change η y * chartMetricForm g p y v w + (1-η y) * inner ℝ v w =
      η y * chartMetricForm g p y w v + (1-η y) * inner ℝ w v
    rw [chartMetricForm_symm, real_inner_comm]
  have hpos : ∀ y v, v ≠ 0 → 0 < B y v v := by
    intro y v hv
    have hip : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    change 0 < η y * chartMetricForm g p y v v + (1-η y) * inner ℝ v v
    by_cases hy : y ∈ (chartAt E p).target
    · have hp := chartMetricForm_pos g p hy hv
      obtain ⟨hη0, hη1⟩ := hηrange y
      by_cases hz : η y = 0
      · simpa only [hz, zero_mul, sub_zero, one_mul, zero_add] using hip
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hη0 (Ne.symm hz)) hp)
          (mul_nonneg (sub_nonneg.mpr hη1) hip.le)
    · have hnV : y ∉ V := fun hyV => hy (hVO (subset_closure hyV))
      simpa only [hηzero y hnV, zero_mul, sub_zero, one_mul, zero_add] using hip
  refine ⟨flatMetricOfForm B hB hsym hpos, ?_⟩
  filter_upwards [hηone] with y hy
  intro v w
  change B y v w = _
  rw [← chartMetricForm_pairing]
  simp [B, hy]
end YauCounterexamples

end

end OAI
