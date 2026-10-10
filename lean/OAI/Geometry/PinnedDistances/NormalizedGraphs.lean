import OAI.Geometry.PinnedDistances.LimitObstruction

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]

/-- Compactness is applied to the four genuine empirical graph laws together.
The only asymptotic hypotheses are the proved test-discrepancy estimates. -/
theorem normalized_graph_impossible
    (G : ∀ n,Core.Fibers (V n) (I n)) (u₁ u₂ : ∀ n,V n → ℂ)
    (x₁ x₂ : ∀ n,V n) (hu₁ : ∀ n,Function.Injective (u₁ n)) (hu₂ : ∀ n,Function.Injective (u₂ n))
    (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
    (hn : ∀ n,2≤Fintype.card (V n))
    (hcard : Tendsto (fun n => (Fintype.card (V n):ℝ)) atTop atTop)
    (C : ℝ) (hC : 0≤C) (hlog₁ : ∀ n,logAverage (u₁ n)≤C) (hlog₂ : ∀ n,logAverage (u₂ n)≤C)
    (hx₁ : ∀ n,(∑ y,logCost (u₁ n) (x₁ n) y)≤C*(Fintype.card (V n):ℝ))
    (hx₂ : ∀ n,(∑ y,logCost (u₂ n) (x₂ n) y)≤C*(Fintype.card (V n):ℝ))
    (hd₁ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (hd₂ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f ((u₂ n x-u₂ n (x₂ n)):Sphere))) atTop (𝓝 0))
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hdR : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y)
    (hrel : ∀ n e y z,y∈(G n).targets e → z∈(G n).targets e →
      (u₁ n y-u₁ n ((G n).source e))*(u₂ n y-u₂ n ((G n).source e))=
      (u₁ n z-u₁ n ((G n).source e))*(u₂ n z-u₂ n ((G n).source e))) : False := by
  let : TopologicalSpace.PseudoMetrizableSpace Sphere := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Quad Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure Sphere) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure (Quad Sphere)) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure (Expanded Sphere)) := inferInstance
  let : CompactSpace (Quad Sphere) := inferInstance
  let : CompactSpace (Expanded Sphere) := inferInstance
  let : CompactSpace (ProbabilityMeasure Sphere) := inferInstance
  let : CompactSpace (ProbabilityMeasure (Quad Sphere)) := inferInstance
  let : CompactSpace (ProbabilityMeasure (Expanded Sphere)) := inferInstance
  let U₁ := fun n x => u₁ n x-u₁ n (x₁ n)
  let U₂ := fun n x => u₂ n x-u₂ n (x₂ n)
  let α₁ := fun n => uniformProbability (fun x => (U₁ n x:Sphere)) (by have:=hn n;omega)
  let α₂ := fun n => uniformProbability (fun x => (U₂ n x:Sphere)) (by have:=hn n;omega)
  let Qn := fun n => edgeProbability (G n) (fun x => (U₁ n x:Sphere))
    (fun x => (U₂ n x:Sphere)) (hG n) (hB n)
  let Rn := fun n => expandedProbability (G n) (fun x => (U₁ n x:Sphere))
    (fun x => (U₂ n x:Sphere)) (hG n) (hB n)
  let L := fun n => (α₁ n,α₂ n,Qn n,Rn n)
  obtain ⟨l,_,φ,hφ,hl⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (L n))
  have ha₁ : Tendsto (α₁ ∘ φ) atTop (𝓝 l.1) := continuous_fst.tendsto l |>.comp hl
  have ha₂ : Tendsto (α₂ ∘ φ) atTop (𝓝 l.2.1) :=
    (continuous_fst.comp continuous_snd).tendsto l |>.comp hl
  have hq : Tendsto (Qn ∘ φ) atTop (𝓝 l.2.2.1) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  have hr : Tendsto (Rn ∘ φ) atTop (𝓝 l.2.2.2) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  let : NullSingletonClass (l.1:Measure Sphere) := normalized_empirical_nonatomic
    (fun n => u₁ (φ n)) (fun n => x₁ (φ n)) (fun n => hu₁ (φ n)) (fun n => hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n => hlog₁ (φ n)) (fun n => hx₁ (φ n)) l.1 ha₁
  let : NullSingletonClass (l.2.1:Measure Sphere) := normalized_empirical_nonatomic
    (fun n => u₂ (φ n)) (fun n => x₂ (φ n)) (fun n => hu₂ (φ n)) (fun n => hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n => hlog₂ (φ n)) (fun n => hx₂ (φ n)) l.2.1 ha₂
  apply graph_limit_impossible (fun n => G (φ n)) (fun n => U₁ (φ n)) (fun n => U₂ (φ n))
    (fun n => hG (φ n)) (fun n => hB (φ n)) (fun n => hn (φ n))
    l.1 l.2.1 l.2.2.1 l.2.2.2 ha₁ ha₂ hq hr
    (fun f => (hd₁ f).comp hφ.tendsto_atTop) (fun f => (hd₂ f).comp hφ.tendsto_atTop)
    (T ∘ φ) (fun n => hT (φ n)) (fun f => (hdR f).comp hφ.tendsto_atTop)
    (ho.comp hφ.tendsto_atTop) M hM (fun n => hdom (φ n))
  intro n e y z hy hz
  simpa only [U₁,U₂,sub_sub_sub_cancel_right] using hrel (φ n) e y z hy hz

end WeakPinned.Bounded

end
end

end OAI
