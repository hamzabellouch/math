import OAI.Geometry.PinnedDistances.FiniteObstruction

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]

/-- The actual finite expanded graph laws cannot have nonatomic coordinate limits
and the two test-independence properties supplied by the variance estimates. -/
theorem graph_limit_impossible
    (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → ℂ)
    (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
    (hn : ∀ n,2≤Fintype.card (V n))
    (β₁ β₂ : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (R : ProbabilityMeasure (Expanded Sphere))
    [NullSingletonClass (β₁:Measure Sphere)] [NullSingletonClass (β₂:Measure Sphere)]
    (hα₁ : Tendsto (fun n => uniformProbability (fun x => (U₁ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂ : Tendsto (fun n => uniformProbability (fun x => (U₂ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ : Tendsto (fun n => edgeProbability (G n) (fun x => (U₁ n x:Sphere))
      (fun x => (U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 Q))
    (hR : Tendsto (fun n => expandedProbability (G n) (fun x => (U₁ n x:Sphere))
      (fun x => (U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 R))
    (hd₁ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (U₁ n x:Sphere))) atTop (𝓝 0))
    (hd₂ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (U₂ n x:Sphere))) atTop (𝓝 0))
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hdR : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x:Sphere))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y)
    (hrel : ∀ n e y z,y∈(G n).targets e → z∈(G n).targets e →
      (U₁ n y-U₁ n ((G n).source e))*(U₂ n y-U₂ n ((G n).source e))=
      (U₁ n z-U₁ n ((G n).source e))*(U₂ n z-U₂ n ((G n).source e))) : False := by
  let : TopologicalSpace.PseudoMetrizableSpace Sphere := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Quad Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere) := inferInstance
  let S₁ := fun n x => (U₁ n x:Sphere)
  let S₂ := fun n x => (U₂ n x:Sphere)
  have hm₁ := expanded_marginal_limit G S₁ S₂ hG hB hn Prod.fst continuous_fst β₁ Q R hα₁ hQ hR hd₁
  have hm₂ := expanded_marginal_limit G S₁ S₂ hG hB hn Prod.snd continuous_snd β₂ Q R hα₂ hQ hR hd₂
  have he := weak_map_eq
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R
    (fun n => edgeProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) Q
    Prod.fst continuous_fst hR hQ
    (fun n => expandedProbability_edge (G n) (S₁ n) (S₂ n) (hG n) (hB n))
  have hi := incoming_limit G S₁ S₂ hG hB hn T hT β₁ Q hα₁ hQ hdR ho
  have hac := edge_ac_limit G S₁ S₂ hG hB hn β₁ β₂ Q hα₁ hα₂ hQ M hM hdom
  have hz := weak_chart_closed expandedCoe expandedCoe_open
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    zEquation zEquation_closed
    (fun n => (expanded_chart_zero (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).1)
  have hw := weak_chart_closed expandedCoe expandedCoe_open
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    wEquation wEquation_closed
    (fun n => (expanded_chart_zero (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).2)
  exact no_sphere_expanded β₁ β₂ Q R he hm₁ hm₂ hi hac.1 hac.2 hz hw

end WeakPinned.Bounded

end
end

end OAI
