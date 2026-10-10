import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal
import OAI.Analysis.BiholderTransport.LinearAlgebra.MaximumPolePositive
import OAI.Analysis.BiholderTransport.Regularity.MaximumPoleSymmetric

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumOuterSamples
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.OuterSampleGood (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k j:ℕ):Prop :=
  let b:=graphBaseCoordinate a (J.samplePoint k j).1
  (∀d e,J.sampleL k j d e=J.sampleL k j e d) ∧
  (∀d,0 ≤ J.sampleL k j d d) ∧
  (∀i,0 ≤ (J.first k).w j i) ∧
  (∀i,chartFiberInverse a b ((J.first k).pj j i)∈
    activeLogs (modifiedDatum v α D (F.b k) Bo) ((extChartAt 𝓘(ℝ,Model n) a).symm b)) ∧
  (∀i,0 < (J.first k).w j i → HasLowerSecondTaylor
    (fun d=>modifiedDatum v α D (F.b k) Bo (movingNormal a (b,(J.first k).pj j i+d))+
      ‖chartFiberInverse a b ((J.first k).pj j i+d)‖^2/2) 0
    ((J.first k).w j i • J.sampleL k j))

lemma MaximumJensenFamily.outer_samples_eventually (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k:ℕ):∀ᶠ j in atTop,J.OuterSampleGood k j := by
  filter_upwards [J.sample_pole_symmetric k,J.sample_pole_positive k,(J.first k).samples]
    with j hs hp hj
  exact ⟨hs,hp,hj.1,hj.2.2.2.1,hj.2.2.2.2⟩

lemma MaximumJensenFamily.exists_outer_diagonal (J:MaximumJensenFamily hmtw hv ho F a c N)
    {ε:ℕ → ℝ} (hε:∀k,0 < ε k):
    Nonempty (MaximumDiagonal J ε J.OuterSampleGood) :=
  J.exists_diagonal hε J.outer_samples_eventually

end MaximumOuterSamples
end WeakMTWTransport

end
end

end OAI
