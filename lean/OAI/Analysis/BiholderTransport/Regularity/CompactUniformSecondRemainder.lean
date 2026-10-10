import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Calculus
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma compact_uniform_second_remainder {Q E : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set Q} (hP : IsCompact P) {F : Q → E → ℝ}
    (hF : ∀ q∈P, ContDiffAt ℝ ∞ (Function.uncurry F) (q,0)) :
    ∃ B>0, ∃ d>0, ∀ q∈P, ∀ z : E, ‖z‖<d →
      |F q z-F q 0-fderiv ℝ (F q) 0 z|≤B*‖z‖^2 := by
  let H := fun w : E×Q => fderiv ℝ (fderiv ℝ (F w.2)) w.1
  have hC : ∀ q∈P, ContinuousAt H (0,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (0,q)) (f := fun w : E×Q => (w.2,w.1))
      (continuousAt_snd.prodMk continuousAt_fst)
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hP
    (f := fun _ : Q => ()) continuous_const (g := fun _ : E => ())
    (continuousAt_const (x := (0:E))) (h := H) (fun q hq _ => hC q hq)
  have HS : ∀ᶠ z : E in 𝓝 0, ∀ q∈P, ()=() → ContDiffAt ℝ 2 (F q) z := by
    apply compact_eventually_fiberwise hP (f := fun _ : Q => ()) continuous_const
      (g := fun _ : E => ()) (continuousAt_const (x := (0:E)))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)
    have hc : ContinuousAt (fun w : E×Q => (w.2,w.1)) (0,q) :=
      continuousAt_snd.prodMk continuousAt_fst
    filter_upwards [hc.tendsto.eventually He] with w hw
    exact hw.comp w.1 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨d,hd,hnear⟩ := Metric.eventually_nhds_iff.mp (HB.and HS)
  refine ⟨B,hB,d,hd,?_⟩
  intro q hq z hz
  have Hrem := first_order_remainder_le_of_hessian_bound (convex_ball (0:E) d) hB.le
    (fun w hw => (hnear hw).2 q hq rfl) (fun w hw => (hnear hw).1 q hq rfl)
    (show (0:E)∈ball 0 d by simpa only [mem_ball,dist_self] using hd)
    (show z∈ball 0 d by simpa only [mem_ball,dist_zero_right] using hz)
  simpa only [sub_zero] using Hrem

end WeakMTWTransport
end
end
end

end OAI
