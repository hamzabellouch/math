import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingHessianLimit
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric
import OAI.Analysis.BiholderTransport.Regularity.OutwardClosed

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameOutwardLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma moving_frame_outward_limit {a:M} {b p r:ℕ → Model n} {q s:Model n}
    {w:ℕ → ℝ} {m μ κ D ν:ℝ}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 q)) (hr:Tendsto r atTop (𝓝 s))
    (hw:Tendsto w atTop (𝓝 m)) (hμ:0 < μ) (hκ:0 < κ) (hD:0 < D) (hν:0 < ν)
    (hsel:∀ᶠ k in atTop,
      let A:=chartFiberInverse a (b k)
      ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ (A (p k)) e ∧ κ*D ≤ (inner ℝ (A (p k)) e)^2 ∧
        0 < d ∧ A (r k)=A (p k)+d • e ∧ μ ≤ w k ∧
        ν*D/(inner ℝ (A (p k)) e) ≤ w k*d ∧
        d ≤ 3*D/(2*(inner ℝ (A (p k)) e))) :
    μ ≤ m ∧ ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
      (show TangentSpace 𝓘(ℝ,Model n) a from s)=(show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
      0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
      κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
      ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m*d ∧
      d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s‖^2-
        ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D := by
  have hbase:(extChartAt 𝓘(ℝ,Model n) a a)∈(extChartAt 𝓘(ℝ,Model n) a).target:=mem_extChartAt_target a
  have hbt:∀ᶠ k in atTop,b k∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hbase)
  have hG:=(frameMetric_continuousAt hbase).tendsto.comp hb
  have hdiff:=hr.sub hp
  have hI:=tendsto_clm_apply (tendsto_clm_apply hG hp) hdiff
  have hN:=tendsto_clm_apply (tendsto_clm_apply hG hdiff) hdiff
  simp only [frameMetric_center] at hI hN
  have H:∀ᶠ k in atTop,μ ≤ w k ∧
      ν*D ≤ w k*frameMetric a (b k) (p k) (r k-p k) ∧
      κ*D*frameMetric a (b k) (r k-p k) (r k-p k) ≤
        (frameMetric a (b k) (p k) (r k-p k))^2 ∧
      frameMetric a (b k) (p k) (r k-p k) ≤ 3*D/2 ∧
      frameMetric a (b k) (r k-p k) (r k-p k) ≤ (9/(4*κ))*D:=by
    filter_upwards [hsel,hbt] with k hk hbk
    dsimp only at hk
    obtain ⟨e,d,he,hep,hq,hd,hrd,hm,hmom,hdb⟩:=hk
    have HH:=outward_closed_conditions he hep hd hrd hκ hD hq hmom hdb
    simp only [frameMetric_apply hbk]
    simp only [map_sub,real_inner_self_eq_norm_sq]
    exact ⟨hm,HH⟩
  have Hm:μ ≤ m:=ge_of_tendsto hw (H.mono (fun k hk=>hk.1))
  refine ⟨Hm,?_⟩
  apply outward_direction_of_closed_conditions (hμ.trans_le Hm) hκ hD hν
  · exact ge_of_tendsto (hw.mul hI) (H.mono (fun k hk=>hk.2.1))
  · have HH:=le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hN) (hI.pow 2)
      (H.mono (fun k hk=>hk.2.2.1))
    rw [show inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from s-q) (s-q)=
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s-q‖^2 from
        @real_inner_self_eq_norm_sq (TangentSpace 𝓘(ℝ,Model n) a) _ _ (s-q)] at HH
    exact HH
  · exact le_of_tendsto hI (H.mono (fun k hk=>hk.2.2.2.1))
  · have HH:=le_of_tendsto hN (H.mono (fun k hk=>hk.2.2.2.2))
    rw [show inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from s-q) (s-q)=
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s-q‖^2 from
        @real_inner_self_eq_norm_sq (TangentSpace 𝓘(ℝ,Model n) a) _ _ (s-q)] at HH
    exact HH

end FrameOutwardLimit
end WeakMTWTransport

end
end

end OAI
