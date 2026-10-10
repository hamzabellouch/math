import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearMatrix

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance frameDetFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance frameDetComplete (x:M) : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) :=
  FiniteDimensional.complete ℝ _

lemma frameMetric_operator {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    bilinearOperator (frameMetric a b)=(chartFiberInverse a b).adjoint.comp (chartFiberInverse a b) := by
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  rw [bilinearOperator_inner,frameMetric_apply hb]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

lemma frameMetric_det {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (bilinearOperator (frameMetric a b)).det=(chartFiberInverse a b).toLinearMap.normDet^2 := by
  rw [frameMetric_operator hb]
  simpa only [RCLike.ofReal_real_eq_id,id_eq] using (chartFiberInverse a b).normDet_sq.symm

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma frameNormDet_pos {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    0<(chartFiberInverse a b).toLinearMap.normDet := by
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm _)
  intro h
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h)
    (LinearMap.ker_eq_bot.mpr (chartFiberInverse_injective hb))

lemma frameNormDet_continuousAt {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContinuousAt (fun z=>(chartFiberInverse a z).toLinearMap.normDet) b := by
  have H:ContinuousAt (fun z=>Real.sqrt (bilinearOperator (frameMetric a z)).det) b := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (bilinear_det_tendsto (frameMetric_continuousAt hb).tendsto)
  apply H.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target _).mem_nhds hb] with z hz
  rw [frameMetric_det hz,Real.sqrt_sq (LinearMap.normDet_nonneg _)]

end FrameDet
end WeakMTWTransport

end
end

end OAI
