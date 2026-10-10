import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumReindex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.comp (J : MaximumJensenFamily hmtw hv ho F a c N)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    MaximumJensenFamily hmtw hv ho (F.comp σ hσ) a c N where
  poleSource k := J.poleSource (σ k)
  endpointSource k := J.endpointSource (σ k)
  sample k := J.sample (σ k)
  first k := J.first (σ k)

def MaximumDiagonal.comp {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    MaximumDiagonal (J.comp σ hσ) (ε ∘ σ) (fun k j=>P (σ k) j) where
  ν := S.ν ∘ σ
  poleSource k := S.poleSource (σ k)
  chart k := S.chart (σ k)
  baseClose k := S.baseClose (σ k)
  velocityClose k := S.velocityClose (σ k)
  centerClose k := S.centerClose (σ k)
  gradientClose k := S.gradientClose (σ k)
  HClose k := S.HClose (σ k)
  LClose k := S.LClose (σ k)
  activeClose k := S.activeClose (σ k)
  weightClose k := S.weightClose (σ k)
  extra k := S.extra (σ k)

lemma MaximumJensenFamily.sampleProjection (J : MaximumJensenFamily hmtw hv ho F a c N)
    (k j:ℕ) :
    graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
      (J.samplePoint k j)=
      (extChartAt 𝓘(ℝ,Model n) c).symm ((J.sample k).z (J.sampleIndex k j)) := by
  exact (hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
    (F.prefixTime k).1 (F.prefixTime k).2).apply_symm_apply _

lemma MaximumDiagonal.endpointSource {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P) (k:ℕ) :
    graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
      (J.samplePoint k (S.ν k))∈(extChartAt 𝓘(ℝ,Model n) c).source := by
  rw [J.sampleProjection]
  exact (extChartAt 𝓘(ℝ,Model n) c).map_target (S.chart k)

lemma MaximumDiagonal.endpointChart {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P) (k:ℕ) :
    extChartAt 𝓘(ℝ,Model n) c
      (graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k)))=(J.sample k).z (J.sampleIndex k (S.ν k)) := by
  rw [J.sampleProjection]
  exact (extChartAt 𝓘(ℝ,Model n) c).right_inv (S.chart k)

end MaximumReindex
end WeakMTWTransport

end
end

end OAI
