import Mathlib
import OAI.Analysis.BiholderTransport.Volume.Measurable
import OAI.Analysis.BiholderTransport.Convexity.TransformSemiconvex

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartAlexandrov
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
omit [Nonempty M] in
lemma original_chart_alexandrov_null {u v:M → ℝ} (hu:Continuous u)
    (hdual:IsCostDualPair u v) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀x∈Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r,x∉N →
        ∃p:Model n,∃A:Model n →L[ℝ] Model n,
          (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
          HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (x+h))) p A := by
  obtain ⟨K,hK,r,hr,ht,hs⟩:=uniform_cTransform_semiconvex (n:=n) a
  have H:=ConvexProximal.ae_quadraticExpansion_semiconvex_open K isOpen_ball (hs u hu) volume
  rw [←hdual.2] at H
  let good:=fun x:Model n=> ∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (x+h))) p A
  let N: Set (Model n):={x | x∈Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r ∧ ¬good x}
  refine ⟨r,hr,N,?_,ht,?_⟩
  · have H':∀ᵐ x:Model n ∂volume,x∉N := H.mono (fun x hx ⟨hb,hbad⟩=>hbad (hx hb))
    rw [ae_iff] at H'
    convert H' using 1
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq,not_not]
  · intro x hx hN
    by_contra hn
    exact hN ⟨hx,hn⟩
end ChartAlexandrov
end WeakMTWTransport

end
end

end OAI
