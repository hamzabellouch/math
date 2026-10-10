import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartTrueMatrix
import OAI.Analysis.BiholderTransport.Convexity.MovingCenterSemibound
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal
import OAI.Analysis.BiholderTransport.Regularity.MaximumEndpoint
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingFamilyHessian

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.center_matrix_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {g:Model n →L[ℝ] ℝ} {B:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hg:Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
    (hB:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 B)) :
    Tendsto (fun k=>J.sampleH k (S.ν k)) atTop
      (𝓝 (chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g B)) := by
  obtain ⟨hb,hp,_,_⟩:=S.limits J hε hQ he
  have hb0:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hc0:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈
      (extChartAt 𝓘(ℝ,Model n) c).source:=by
    rw [movingPrefix_at_center,one_smul,he]
    exact mem_extChartAt_source c
  have hn:∀ᶠ k in atTop,(∀ᶠ z in 𝓝 ((J.sample k).z (J.sampleIndex k (S.ν k))),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
          ((J.sample k).z (J.sampleIndex k (S.ν k))):=by
    apply Eventually.of_forall
    intro k
    refine ⟨?_,((J.sample k).samples (J.sampleIndex k (S.ν k))).2.2.2.2.2.2.2.2.1⟩
    filter_upwards [(J.sample k).openRegion.mem_nhds
      ((J.sample k).sampleInRegion (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  have HC:=moving_family_rough_hessian_limit
    (f:=fun k=>chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
    (g:=fun z:ℝ×Model n=>movingPrefixChart a c z.1 z.2)
    (joint_movingPrefixChart_contDiffAt hb0 hc0) (F.time.prodMk_nhds hb) hp
    (by simpa only [S.movingChart] using hg) (by simpa only [S.movingChart] using hB)
    (by simpa only [S.movingChart] using hn)
  have HE:=moving_energy_hessian_tendsto hq hb hp F.time
  have heq:fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 (extChartAt 𝓘(ℝ,Model n) a a))) q=
      frameMetric a (extChartAt 𝓘(ℝ,Model n) a a):=by
    ext d e
    rw [movingPrefixEnergy_hessian_at_center hq,frameMetric_center]
  rw [heq] at HE
  have HT:=HE.add HC
  apply HT.congr'
  apply Eventually.of_forall
  intro k
  have hc:movingPrefix a (F.t k) (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)∈
        (extChartAt 𝓘(ℝ,Model n) c).source:=by
    rw [movingPrefix_graph_coordinates (S.poleSource k)]
    exact S.endpointSource k
  exact (coordinateCenterMatrix_chart
    ((extChartAt 𝓘(ℝ,Model n) a).map_source (S.poleSource k)) hc).symm

lemma MaximumDiagonal.center_matrix_le_pole_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0))
    {H L:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hH:Tendsto (fun k=>J.sampleH k (S.ν k)) atTop (𝓝 H))
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L)) (d:Model n) : H d d ≤ L d d := by
  have hhh:Tendsto (fun k=>J.sampleH k (S.ν k) d d) atTop (𝓝 (H d d)):=tendsto_clm_apply (tendsto_clm_apply hH tendsto_const_nhds) tendsto_const_nhds
  have hll:Tendsto (fun k=>(J.first k).L d d) atTop (𝓝 (L d d)):=tendsto_clm_apply (tendsto_clm_apply hL tendsto_const_nhds) tendsto_const_nhds
  have HE:=hε.mul_const (‖d‖^2)
  have HI:∀ᶠ k in atTop,J.sampleH k (S.ν k) d d ≤ (J.first k).L d d+ε k*‖d‖^2:=by
    apply Eventually.of_forall
    intro k
    exact (bilinear_quadratic_close (S.HClose k).le d).trans
      (add_le_add ((J.first k).upper d) le_rfl)
  simpa only [zero_mul,add_zero] using le_of_tendsto_of_tendsto hhh (hll.add HE) HI
end MaximumCenterLimit
end WeakMTWTransport

end
end

end OAI
