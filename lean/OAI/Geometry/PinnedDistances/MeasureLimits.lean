import OAI.Geometry.PinnedDistances.ProductLimits

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction NNReal ENNReal
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → Sphere)
  (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
  (hn : ∀ n,2≤Fintype.card (V n))

lemma expanded_marginal_limit (π : Sphere × Sphere → Sphere) (hπ : Continuous π)
    (β : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (R : ProbabilityMeasure (Expanded Sphere))
    (hα : Tendsto (fun n => uniformProbability (fun x => π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hR : Tendsto (fun n => expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 R))
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0)) :
    (R:Measure (Expanded Sphere)).map (fun r => (r.1,(π r.2.1,π r.2.2)))=
      (Q:Measure (Quad Sphere)).prod ((β:Measure Sphere).prod β) := by
  apply weak_double_product_limit (fun n => expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) R
    (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
    (fun n => uniformProbability (fun x => π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) β
    Prod.fst (fun r => π r.2.1) (fun r => π r.2.2) continuous_fst
    (hπ.comp (continuous_fst.comp continuous_snd)) (hπ.comp (continuous_snd.comp continuous_snd)) hR hQ hα
  exact expanded_test_rate G U₁ U₂ hG hB hn π hd

lemma incoming_limit (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (β : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (hα : Tendsto (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0)) :
    (Q:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2))=
      (β:Measure Sphere).prod ((Q:Measure (Quad Sphere)).map (fun q => q.2.2)) := by
  let Qn := fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)
  have hc : Continuous (fun q : Quad Sphere => (q.1,q.2.2)) := by fun_prop
  have ht : Continuous (fun q : Quad Sphere => q.2.2) := by fun_prop
  apply weak_pair_product_limit (fun n => (Qn n).map (fun q => (q.1,q.2.2)))
    (Q.map (fun q => (q.1,q.2.2)))
    (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) β
    (fun n => (Qn n).map (fun q => q.2.2)) (Q.map (fun q => q.2.2))
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ hc) hα
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ ht)
  intro f g
  have hh := incoming_law_test_rate G U₁ U₂ hG hB hn T hT hd ho f g
  convert hh using 1
  funext n
  change (∫ q,f q.1*g q.2 ∂ (Qn n:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2)))-
    (∫ z,f z ∂ uniformLaw (U₁ n))*(∫ p,g p ∂ (Qn n:Measure (Quad Sphere)).map (fun q => q.2.2))=_
  rw [integral_map_of_stronglyMeasurable hc.measurable (by fun_prop),
    integral_map_of_stronglyMeasurable ht.measurable g.continuous.stronglyMeasurable]

lemma edge_ac_limit (β₁ β₂ : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (hα₁ : Tendsto (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂ : Tendsto (fun n => uniformProbability (U₂ n) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y) :
    (Q:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2.1))≪(β₁:Measure Sphere).prod β₁ ∧
    (Q:Measure (Quad Sphere)).map (fun q => (q.2.1,q.2.2.2))≪(β₂:Measure Sphere).prod β₂ := by
  let c : ℝ≥0 := ⟨2*M,by positivity⟩
  have hc : (c:ℝ≥0∞)=ENNReal.ofReal (2*M) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  constructor
  · apply weak_map_domination
      (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n => (uniformProbability (U₁ n) (by have:=hn n;omega)).prod
        (uniformProbability (U₁ n) (by have:=hn n;omega))) (β₁.prod β₁)
      (fun q => (q.1,q.2.2.1)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₁,β₁) |>.comp (hα₁.prodMk_nhds hα₁)) c
    intro n
    rw [hc]
    exact edgeProbability_dom₁ (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)
  · apply weak_map_domination
      (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n => (uniformProbability (U₂ n) (by have:=hn n;omega)).prod
        (uniformProbability (U₂ n) (by have:=hn n;omega))) (β₂.prod β₂)
      (fun q => (q.2.1,q.2.2.2)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₂,β₂) |>.comp (hα₂.prodMk_nhds hα₂)) c
    intro n
    rw [hc]
    exact edgeProbability_dom₂ (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma quadCoe_range (q : Quad Sphere)
    (h₁ : (q.1,q.2.2.1)∈range pairCoe) (h₂ : (q.2.1,q.2.2.2)∈range pairCoe) :
    q∈range quadCoe := by
  obtain ⟨⟨a,c⟩,ha⟩ := h₁
  obtain ⟨⟨b,d⟩,hb⟩ := h₂
  exact ⟨(a,b,c,d),by ext <;> simp_all [pairCoe,quadCoe,Prod.mk.injEq]⟩

lemma expandedCoe_range (r : Expanded Sphere)
    (h₁ : (r.1,(r.2.1.1,r.2.2.1))∈range (Prod.map quadCoe pairCoe))
    (h₂ : (r.1,(r.2.1.2,r.2.2.2))∈range (Prod.map quadCoe pairCoe)) :
    r∈range expandedCoe := by
  obtain ⟨⟨q,z,w⟩,hz⟩ := h₁
  obtain ⟨⟨q',v,t⟩,hv⟩ := h₂
  refine ⟨(q,((z,v),(w,t))),?_⟩
  have he : quadCoe q=r.1 := congrArg Prod.fst hz
  have hz' := congrArg Prod.snd hz
  have hv' := congrArg Prod.snd hv
  apply Prod.ext he
  dsimp [expandedCoe]
  ext <;> simp_all [pairCoe,Prod.mk.injEq]

lemma map_transport_ac {A : Type u3} {B : Type u4} {X : Type u5} {Y : Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j : A → X) (k : B → Y)
    (hj : Measurable j) (hk : MeasurableEmbedding k)
    (f : A → B) (g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure A) (ν : Measure B) (hcomm : k ∘ f=g ∘ j)
    (hm : (μ.map j).map g≪ν.map k) : μ.map f≪ν := by
  apply map_pull_ac k hk
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm

lemma sphere_quad_finite (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (Quad Sphere))
    (h₁ : Q.map (fun q => (q.1,q.2.2.1))≪(μ.map OnePoint.some).prod (μ.map OnePoint.some))
    (h₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪(ν.map OnePoint.some).prod (ν.map OnePoint.some)) :
    ∀ᵐ q ∂ Q,q∈range quadCoe := by
  have hpμ := map_full_range pairCoe pairCoe_open.measurableEmbedding (μ.prod μ)
  have hpν := map_full_range pairCoe pairCoe_open.measurableEmbedding (ν.prod ν)
  rw [← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable] at hpμ hpν
  have hq₁ := (ae_map_iff (by fun_prop) pairCoe_open.measurableEmbedding.measurableSet_range).mp
    (h₁.ae_le hpμ)
  have hq₂ := (ae_map_iff (by fun_prop) pairCoe_open.measurableEmbedding.measurableSet_range).mp
    (h₂.ae_le hpν)
  exact (hq₁.and hq₂).mono (fun q h => quadCoe_range q h.1 h.2)

lemma sphere_expanded_finite (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded Sphere)) [IsProbabilityMeasure Q]
    (h₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=
      (Q.map quadCoe).prod ((μ.map OnePoint.some).prod (μ.map OnePoint.some)))
    (h₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=
      (Q.map quadCoe).prod ((ν.map OnePoint.some).prod (ν.map OnePoint.some))) :
    ∀ᵐ r ∂ R,r∈range expandedCoe := by
  have hj := quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding
  have hpμ := map_full_range _ hj (Q.prod (μ.prod μ))
  have hpν := map_full_range _ hj (Q.prod (ν.prod ν))
  rw [← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
    pairCoe_open.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable,← h₁] at hpμ
  rw [← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
    pairCoe_open.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable,← h₂] at hpν
  have hq₁ := (ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpμ
  have hq₂ := (ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpν
  exact (hq₁.and hq₂).mono (fun r h => expandedCoe_range r h.1 h.2)

end WeakPinned.Bounded

end
end

end OAI
