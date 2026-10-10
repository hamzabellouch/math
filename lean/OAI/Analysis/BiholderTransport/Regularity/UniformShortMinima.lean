import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LocalMountains
import OAI.Analysis.BiholderTransport.LinearAlgebra.DiagonalCostConvexity
import OAI.Analysis.BiholderTransport.Coordinates.ShortLocalMinimum

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
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [Nonempty M] in
lemma exists_parametric_short_action_local_minima {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ r>0, ∃ V∈𝓝 ((p,(0:ℝ)),x), ∀ q∈V, ∀ y∈Metric.closedBall x r,
      fderiv ℝ (fun w => q.1.2*ψ (q.1.1,w)+
        chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) w) y=0 →
      ∀ w∈Metric.closedBall x r, q.1.2*ψ (q.1.1,y)+
        chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) y≤
          q.1.2*ψ (q.1.1,w)+chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) w := by
  let F : ((P×ℝ)×Model n) → Model n → ℝ := fun q y =>
    q.1.2*ψ (q.1.1,y)+chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) y
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (((p,(0:ℝ)),x),x) :=
    (contDiffAt_fst.fst.snd.mul (hψ.comp (f := fun q : ((P×ℝ)×Model n)×Model n => (q.1.1.1,q.2)) _
      (contDiffAt_fst.fst.fst.prodMk contDiffAt_snd))).add
      ((chartCost_pair_contDiffAt_diagonal (a := a) (x := x) hx).comp (((p,(0:ℝ)),x),x)
        (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hswap : ContinuousAt (fun q : Model n×((P×ℝ)×Model n) => q.swap) (x,((p,(0:ℝ)),x)) :=
    continuousAt_snd.prodMk continuousAt_fst
  have hH : ContinuousAt (fun q : Model n×((P×ℝ)×Model n) =>
      fderiv ℝ (fderiv ℝ (F q.2)) q.1) (x,((p,(0:ℝ)),x)) := by
    have H := (ContDiffAt.partial_snd_fderiv_two (f := F) hF).continuousAt.comp
      (x := (x,((p,(0:ℝ)),x))) hswap
    exact H
  have hD : ∀ᶠ q : Model n×((P×ℝ)×Model n) in 𝓝 (x,((p,(0:ℝ)),x)),
      ContDiffAt ℝ 2 (F q.2) q.1 := by
    have H := hswap.eventually ((hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp))
    filter_upwards [H] with q hq
    exact hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨m,hm,hpos⟩ := chartCost_diagonal_coercive hx
  have heq : F ((p,0),x)=chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm x) := by
    ext y; simp only [F,zero_mul,zero_add]
  have hposF : ∀ d, m*‖d‖^2≤fderiv ℝ (fderiv ℝ (F ((p,0),x))) x d d := by
    rw [heq]
    exact hpos
  exact exists_local_mountains hm hH hD hposF

end WeakMTWTransport

end

end OAI
