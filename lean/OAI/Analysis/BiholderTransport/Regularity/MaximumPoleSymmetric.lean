import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily
import OAI.Analysis.BiholderTransport.Regularity.MaximumSample
import OAI.Analysis.BiholderTransport.Regularity.MaximumReindex

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumPoleSymmetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.sample_pole_symmetric (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k:ℕ) : ∀ᶠ j in atTop,∀d e:Model n,J.sampleL k j d e=J.sampleL k j e d := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  let v0:=modifiedDatum v α D (F.b k) Bo
  have hv0:=continuous_modifiedDatum hv α D (F.b k) ho
  have ht:=(F.prefixTime k).1
  have ht1:=(F.prefixTime k).2
  have hσ:=(J.first k).strictMono.tendsto_atTop
  obtain ⟨hQ,hb,hp⟩:=(F.row k).jensen_graph_limit hmtw hv ho ht ht1
    (J.sample k) (J.endpointSource k) (J.poleSource k)
  have hbase: Tendsto (fun j=>(J.samplePoint k j).1.1) atTop (𝓝 (F.row k).q.1.1) :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto (F.row k).q.1
      |>.comp (hQ.comp hσ)
  have ha:=hbase.eventually ((isOpen_extChartAt_source _).mem_nhds (J.poleSource k))
  have hd:=hbase.eventually ((isOpen_extChartAt_source (F.row k).q.1.1).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) (F.row k).q.1.1))
  have hz:=((J.sample k).points.comp hσ).eventually ((isOpen_extChartAt_target c).mem_nhds
    (χ.map_source (J.endpointSource k)))
  have hpole:chartActualPole v0 (F.t k) c (χ (F.z k))=(F.row k).q.1.1 := by
    dsimp only [chartActualPole]
    rw [χ.left_inv (J.endpointSource k)]
    rw [←hmtw.graphHomeomorph_inverse_pole hv0 ht ht1 (F.z k)]
    exact congrArg (fun q=>q.1.1) ((F.row k).graph_inverse hmtw hv ho ht ht1)
  filter_upwards [ha,hd,hz] with j haj hdj hzj
  let q:=J.samplePoint k j
  let b:=graphBaseCoordinate a q.1
  let p:=graphVelocityCoordinate a q.1
  have hbt:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source haj
  have he:movingPrefix a (F.t k) b p=graphProjection (cTransform v0) (F.t k) q :=
    movingPrefix_graph_coordinates haj (F.t k)
  have hec:χ (movingPrefix a (F.t k) b p)=(J.sample k).z (J.sampleIndex k j) := by
    rw [he,J.sampleProjection]
    exact χ.right_inv hzj
  have hs:movingPrefix a (F.t k) b p∈χ.source := by
    rw [he,J.sampleProjection]
    exact χ.map_target hzj
  have hbd:(extChartAt 𝓘(ℝ,Model n) a).symm b∈
      (extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1).source := by
    change (extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a q.1.1)∈_
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv haj]
    exact hdj
  have hD: DifferentiableAt ℝ (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1
      (hopfPole (n := n) (F.t k) (cTransform v0) (χ.symm w)))
      (χ (movingPrefix a (F.t k) b p)) := by
    rw [hec,←hpole]
    exact ((J.sample k).samples (J.sampleIndex k j)).2.2.2.2.2.1.differentiableAt
  exact (hmtw.coordinate_sample_pole_matrix hv0 ht ht1 hbt
    (graphCoordinate_normalSubdifferential q haj) hs hbd hD).2.1

end MaximumPoleSymmetric
end WeakMTWTransport

end
end

end OAI
