import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily
import OAI.Analysis.BiholderTransport.Regularity.MaximumSample
import OAI.Analysis.BiholderTransport.Regularity.Diagonal

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

abbrev MaximumJensenFamily.sampleIndex (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :=
  (J.first k).σ j

def MaximumJensenFamily.samplePoint (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    subgradientGraph (n := n) (cTransform (modifiedDatum v α D (F.b k) Bo)) :=
  (hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
    (F.prefixTime k).1 (F.prefixTime k).2).symm
      ((extChartAt 𝓘(ℝ,Model n) c).symm ((J.sample k).z (J.sampleIndex k j)))

def MaximumJensenFamily.sampleCenter (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) : Model n :=
  extChartAt 𝓘(ℝ,Model n) c ((J.sample k).Y ((J.sample k).z (J.sampleIndex k j)))

def MaximumJensenFamily.sampleGradient (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] ℝ :=
  fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c)
      ((J.sample k).z (J.sampleIndex k j))+
    fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
      ((J.sample k).z (J.sampleIndex k j))

def MaximumJensenFamily.sampleH (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  coordinateCenterMatrix a (F.t k) (hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (graphBaseCoordinate a (J.samplePoint k j).1) (graphVelocityCoordinate a (J.samplePoint k j).1)

def MaximumJensenFamily.sampleL (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  coordinatePoleMatrix a (F.t k) (modifiedDatum v α D (F.b k) Bo)
    (graphBaseCoordinate a (J.samplePoint k j).1) (graphVelocityCoordinate a (J.samplePoint k j).1)

structure MaximumDiagonal (J : MaximumJensenFamily hmtw hv ho F a c N)
    (ε : ℕ → ℝ) (P : ℕ → ℕ → Prop) where
  ν : ℕ → ℕ
  poleSource : ∀ k,(J.samplePoint k (ν k)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source
  chart : ∀ k,(J.sample k).z (J.sampleIndex k (ν k))∈(extChartAt 𝓘(ℝ,Model n) c).target
  baseClose : ∀ k,dist (graphBaseCoordinate a (J.samplePoint k (ν k)).1)
    (graphBaseCoordinate a (F.row k).q.1)<ε k
  velocityClose : ∀ k,dist (graphVelocityCoordinate a (J.samplePoint k (ν k)).1)
    (graphVelocityCoordinate a (F.row k).q.1)<ε k
  centerClose : ∀ k,dist (J.sampleCenter k (ν k))
    (extChartAt 𝓘(ℝ,Model n) c (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2))<ε k
  gradientClose : ∀ k,‖J.sampleGradient k (ν k)‖<ε k
  HClose : ∀ k,‖J.sampleH k (ν k)-(J.first k).H‖<ε k
  LClose : ∀ k,‖J.sampleL k (ν k)-(J.first k).L‖<ε k
  activeClose : ∀ k,dist ((J.first k).pj (ν k)) (J.first k).pj₀<ε k
  weightClose : ∀ k,dist ((J.first k).w (ν k)) (J.first k).w₀<ε k
  extra : ∀ k,P k (ν k)

lemma MaximumJensenFamily.exists_diagonal (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} (hε : ∀ k,0<ε k) {P : ℕ → ℕ → Prop}
    (hP : ∀ k,∀ᶠ j in atTop,P k j) : Nonempty (MaximumDiagonal J ε P) := by
  have H (k:ℕ) := (F.row k).jensen_approximation hmtw hv ho (F.prefixTime k).1
    (F.prefixTime k).2 (J.sample k) (J.endpointSource k) (J.poleSource k) (J.first k)
    (ε k) (hε k) (P k) (hP k)
  choose ν hs hc hb hp hy hg hH hL hi hw hex using H
  exact ⟨⟨ν,hs,hc,hb,hp,hy,hg,hH,hL,hi,hw,hex⟩⟩

lemma MaximumDiagonal.limits (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hε : Tendsto ε atTop (𝓝 0)) {q : Model n}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) (hc : riemannianExp a q=c) :
    Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q) ∧
    Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) ∧
    Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0) := by
  obtain ⟨hb,hp,hz,hy⟩ := F.limit_coordinates hQ
  rw [hc] at hy
  have hY := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hy
  refine ⟨diagonal_tendsto_of_close hb hε (Eventually.of_forall (fun k=>(S.baseClose k).le)),
    diagonal_tendsto_of_close hp hε (Eventually.of_forall (fun k=>(S.velocityClose k).le)),
    diagonal_tendsto_of_close hY hε (Eventually.of_forall (fun k=>(S.centerClose k).le)),?_⟩
  apply diagonal_tendsto_of_close tendsto_const_nhds hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_zero_right] using (S.gradientClose k).le)

end WeakMTWTransport

end

end OAI
