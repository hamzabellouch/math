import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingHessianLimit
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearAbsorption

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameAbsorption
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventual_frame_rank_lower {a:M} {b p:ℕ → Model n} {q:Model n}
    {H:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ} {A C:ℝ} (hA:0<A)
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 q))
    (hH:∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2≤H k d d) :
    ∀ᶠ k in atTop,∀d:Model n,
      A/2*‖chartFiberInverse a (b k) d‖^2+
        C*(inner ℝ (chartFiberInverse a (b k) (p k)) (chartFiberInverse a (b k) d))^2≤H k d d := by
  let b₀ := extChartAt 𝓘(ℝ,Model n) a a
  have hb₀ : b₀∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hG := (frameMetric_continuousAt hb₀).tendsto.comp hb
  have hR := covectorSquare_continuous.tendsto (frameMetric a b₀ q) |>.comp (tendsto_clm_apply hG hp)
  obtain ⟨δ,hδ,hcoer⟩ := frameMetric_center_coercive (n := n) a
  have HH : ∀ε:ℝ,0<ε → ∀ᶠ k in atTop,∀d:Model n,
      A*frameMetric a b₀ d d+C*covectorSquare (frameMetric a b₀ q) d d-ε*‖d‖^2≤H k d d := by
    intro ε he
    filter_upwards [hH ε he] with k hk
    intro d
    have hself : frameMetric a b₀ d d=‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2 := by
      exact (frameMetric_center a d d).trans
        (real_inner_self_eq_norm_sq (show TangentSpace 𝓘(ℝ,Model n) a from d))
    simpa only [hself,covectorSquare_apply,frameMetric_center,←sq,b₀] using hk d
  have HG := eventual_moving_rank_lower hA hδ hcoer hG hR HH
  have ht : ∀ᶠ k in atTop,b k∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb₀)
  filter_upwards [HG,ht] with k hk hbk
  intro d
  simpa only [Function.comp_def,covectorSquare_apply,frameMetric_apply hbk,real_inner_self_eq_norm_sq,←sq] using hk d

end FrameAbsorption
end WeakMTWTransport

end
end

end OAI
