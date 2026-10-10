import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.JointMovingPrefix
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal
import OAI.Analysis.BiholderTransport.Regularity.MaximumReindex

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.movingChart {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (k:ℕ) :
    movingPrefixChart a c (F.t k) (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)=
        (J.sample k).z (J.sampleIndex k (S.ν k)) := by
  rw [movingPrefixChart,movingPrefix_graph_coordinates (S.poleSource k)]
  exact S.endpointChart k

lemma MaximumDiagonal.endpoint_tendsto {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {q:Model n} (hc:riemannianExp a q=c)
    (hb:Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q)) :
    Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) := by
  have hb0:extChartAt 𝓘(ℝ,Model n) a a∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have H:=((joint_movingPrefixChart_contDiffAt hb0 hgc).continuousAt.tendsto).comp
    ((F.time.prodMk_nhds hb).prodMk_nhds hp)
  change Tendsto (fun k=>movingPrefixChart a c (F.t k)
    (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
    (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)) atTop
    (𝓝 (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a) q)) at H
  simp only [S.movingChart] at H
  simpa only [movingPrefixChart,movingPrefix_at_center,one_smul,hc] using H

end MaximumEndpoint
end WeakMTWTransport

end
end

end OAI
