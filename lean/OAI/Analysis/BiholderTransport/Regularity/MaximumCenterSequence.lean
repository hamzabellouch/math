import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamily
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal
import OAI.Analysis.BiholderTransport.Regularity.MaximumReindex
import OAI.Analysis.BiholderTransport.Convexity.JensenAtCenter
import OAI.Analysis.BiholderTransport.Regularity.SampleCenterFamilies

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterSequence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.sampleSlope (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) : ℝ :=
  deriv (fun s=>modifiedScalar α D Bc (F.b k,s))
    (v ((J.sample k).Y ((J.sample k).z (J.sampleIndex k j))))

lemma MaximumDiagonal.center_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>(J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 c) := by
  let χ := extChartAt 𝓘(ℝ,Model n) c
  have H := (continuousAt_extChartAt_symm'' (χ.map_source (mem_extChartAt_source c))).tendsto.comp hx
  rw [χ.left_inv (mem_extChartAt_source c)] at H
  apply H.congr
  intro k
  exact χ.left_inv ((J.sample k).samples (J.sampleIndex k (S.ν k))).1

lemma MaximumDiagonal.slope_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hBc : ContDiff ℝ ∞ Bc) {β : ℝ} (hβ : Tendsto F.b atTop (𝓝 β))
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>J.sampleSlope k (S.ν k)) atTop
      (𝓝 (deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c))) := by
  exact ((continuous_scalar_family_deriv (modifiedScalar_contDiff hBc α D)).tendsto (β,v c)).comp
    (hβ.prodMk_nhds ((hv.tendsto c).comp (S.center_tendsto hx)))

def MaximumDiagonal.center_sequence {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    {u : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hLv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) (hBc : ContDiff ℝ ∞ Bc)
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (hl : ∀ k,0<J.sampleSlope k (S.ν k) ∧ J.sampleSlope k (S.ν k)<1)
    (hg : Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0)) :
    CenterSequenceData a c u v (modifiedScalar α D Bc) F.b
      (fun k=>J.sampleSlope k (S.ν k)) (fun k=>1-F.t k) F.t
      (fun k=>J.sampleCenter k (S.ν k))
      (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)
      (fun k=>graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k)))
      (fun k=>chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c) := by
  have R (k:ℕ) : Nonempty (TrueCenterRow c u v
      (fun s=>modifiedScalar α D Bc (F.b k,s)) (J.sampleCenter k (S.ν k))
      (graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k))) (1-F.t k) (J.sampleSlope k (S.ν k))) := by
    rw [J.sampleProjection]
    exact hmtw.jensen_at_center_row hu hLv hdual
      ((modifiedScalar_contDiff hBc α D).continuous.comp (continuous_const.prodMk continuous_id))
      (hmono (F.b k) (Ioo_subset_Icc_self (F.parameter k)))
      (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (J.sampleIndex k (S.ν k))
      (scalar_family_derivable (modifiedScalar_contDiff hBc α D)
        (F.b k,v ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))))) (hl k).1 (hl k).2
  apply hmtw.center_sequence_of_graph
    (fun k=>continuous_modifiedDatum hv α D (F.b k) ho)
    (fun k=>(F.prefixTime k).1) (fun k=>(F.prefixTime k).2)
    (fun k=>J.samplePoint k (S.ν k)) S.poleSource S.endpointSource
    (fun k=>Classical.choice (R k))
  · apply Eventually.of_forall
    intro k
    rw [S.endpointChart]
    obtain ⟨_,_,_,_,_,_,_,_,hC,_,_⟩ := (J.sample k).samples (J.sampleIndex k (S.ν k))
    refine ⟨?_,hC⟩
    filter_upwards [(J.sample k).openRegion.mem_nhds ((J.sample k).sampleInRegion
      (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  · convert hg using 1
    ext k
    rw [S.endpointChart]
    rfl

end MaximumCenterSequence
end WeakMTWTransport

end
end

end OAI
