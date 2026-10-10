import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GlobalFlow

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentScale_continuous :
    Continuous (fun q : ℝ × TangentBundle (model n) M => mulState q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s,p⟩
  let e := trivializationAt (Model n) (TangentSpace (model n)) p.1
  have hpe : p ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) p.1)
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.comp continuous_snd).continuousAt
  · have hpE : ContinuousAt (fun q : ℝ × TangentBundle (model n) M => (e q.2).2) (s,p) :=
      continuousAt_snd.comp ((e.continuousAt hpe).comp continuousAt_snd)
    have hc := continuousAt_fst.smul hpE
    apply hc.congr_of_eventuallyEq
    have hnear : ∀ᶠ q : ℝ × TangentBundle (model n) M in 𝓝 (s,p), q.2 ∈ e.source :=
      continuousAt_snd.preimage_mem_nhds (e.open_source.mem_nhds hpe)
    filter_upwards [hnear] with q hq
    have hb := e.mem_source.mp hq
    change (e (⟨q.2.1,q.1•q.2.2⟩ : TangentBundle (model n) M)).2 = q.1 • (e q.2).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hb,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hb,map_smul]

 theorem scaledExp_smooth (s : ℝ) :
    ContMDiff ((model n).prod (model n)) (model n) ∞
      (fun p : TangentBundle (model n) M => exp p.1 (s•p.2)) := by
  have hh := (contMDiff_proj (TangentSpace (model n))).comp
    (geodesicFlow_smooth_fixed (n := n) (M := M) s)
  convert hh using 1
  funext p
  exact exp_mul_eq_geodesic p s

 theorem scaledExp_continuous :
    Continuous (fun q : ℝ × TangentBundle (model n) M => exp q.2.1 (q.1•q.2.2)) :=
    exp_total_smooth.continuous.comp tangentScale_continuous

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
