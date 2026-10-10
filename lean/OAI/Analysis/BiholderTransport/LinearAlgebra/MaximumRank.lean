import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily
import OAI.Analysis.BiholderTransport.Regularity.FrameAbsorption
import OAI.Analysis.BiholderTransport.LinearAlgebra.FirstRank
import OAI.Analysis.BiholderTransport.Coordinates.ChartParameter

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumRank
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.eventual_rank_of_center_lower
    {hmtw:WeakMTW (n := n) (M := M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n := n) v α D bminus bplus Bc Bo}
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A)
    (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
          (J.first k).H d d) :
    ∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let p:=graphVelocityCoordinate a (F.row k).q.1
      let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
      let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < (J.first k).w₀ i}
      let pj:κ → E:=fun i=>chartFiberInverse a b ((J.first k).pj₀ i)
      let P:E:=chartFiberInverse a b p
      let S:=Submodule.span ℝ (range (fun i=>pj i-P))
      ∃ e∈S,‖e‖=1 ∧ 0 < inner ℝ P e ∧ S=Submodule.span ℝ {e} ∧
        A/2 ≤ (-C)*(inner ℝ P e)^2 := by
  obtain ⟨hb,hpcoord,_,_⟩:=F.limit_coordinates hQ
  have H:=eventual_frame_rank_lower hA hb hpcoord hH
  filter_upwards [H] with k hk
  let b:=graphBaseCoordinate a (F.row k).q.1
  let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  let level:E → ℝ:=fun r=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) r)-α)/D
  have hbt:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have Hb:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have Hpos:0 < (1:ℝ)/4096+4*F.b k/bplus := by positivity
  have HP:0 < Bc (level (chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)))-
      ∑ i,(J.first k).w₀ i*Bo (level (chartFiberInverse a b ((J.first k).pj₀ i))) := by
    have HP:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
    change 1/4096+4*F.b k/bplus ≤
      Bc ((v (movingNormal a (b,graphVelocityCoordinate a (F.row k).q.1))-α)/D)-
        ∑ i,(J.first k).w₀ i*Bo ((v (movingNormal a (b,(J.first k).pj₀ i))-α)/D) at HP
    simp only [movingNormal_eq hbt] at HP
    exact Hpos.trans_le HP
  exact (J.first k).positive_rank_direction (J.poleSource k) (A/2) C (half_pos hA) hk
    level Bc Bo (hprofiles _) HP

end MaximumRank
end WeakMTWTransport

end
end

end OAI
