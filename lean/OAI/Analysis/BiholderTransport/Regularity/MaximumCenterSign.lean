import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily
import OAI.Analysis.BiholderTransport.Coordinates.ChartParameter

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterSign
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.center_parameter_bound
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hb:∀s,0 ≤ Bo s) (k:ℕ) :
    (1:ℝ)/4096 ≤ Bc ((v (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2)-α)/D) := by
  have H:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
  dsimp only at H
  have hs:0 ≤ ∑i,(J.first k).w₀ i*Bo ((v (movingNormal a
      (graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ i))-α)/D) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg ((J.first k).nonnegLimit i) (hb _)
  have hp':0 ≤ 4*F.b k/bplus:=div_nonneg (mul_nonneg (by norm_num)
    (hm.trans (F.parameter k).1.le)) hp.le
  have hbt:graphBaseCoordinate a (F.row k).q.1∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have heq:movingNormal a (graphBaseCoordinate a (F.row k).q.1,
      graphVelocityCoordinate a (F.row k).q.1)=riemannianExp (F.row k).q.1.1 (F.row k).q.1.2 := by
    rw [movingNormal_eq hbt]
    exact congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2)
      (graph_coordinate_reconstruction (J.poleSource k))
  rw [heq] at H
  linarith only [H,hs,hp']

lemma MaximumJensenFamily.center_limit_positive
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hb:∀s,0 ≤ Bo s) (hc:Continuous Bc)
    {q:Model n} (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) :
    (1:ℝ)/4096 ≤ Bc ((v c-α)/D) := by
  have H:=(F.limit_coordinates hQ).2.2.2
  rw [he] at H
  exact ge_of_tendsto (hc.continuousAt.tendsto.comp
    (((hv.continuousAt.tendsto.comp H).sub_const α).div_const D))
    (Eventually.of_forall (J.center_parameter_bound hm hp hb))

end MaximumCenterSign
end WeakMTWTransport

end
end

end OAI
