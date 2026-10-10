import OAI.Geometry.PinnedDistances.FiniteMixtures

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

variable {X : Type u1} {Y : Type u2} [MeasurableSpace X] [MeasurableSpace Y]

lemma chart_probability (j : X → Y) (hj : MeasurableEmbedding j)
    (μ : Measure Y) [IsProbabilityMeasure μ] (hfin : ∀ᵐ y ∂  μ,y∈range j) :
    IsProbabilityMeasure (μ.comap j) := by
  constructor
  rw [hj.comap_apply,image_univ]
  exact measure_eq_measure_of_null_sdiff (subset_univ _) (by
    convert ae_iff.mp hfin using 2
    ext y
    simp) |>.trans measure_univ

lemma chart_map_comap (j : X → Y) (hj : MeasurableEmbedding j)
    (μ : Measure Y) (hfin : ∀ᵐ y ∂  μ,y∈range j) : (μ.comap j).map j=μ := by
  rw [hj.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem hfin

lemma chart_ae_iff (j : X → Y) (hj : MeasurableEmbedding j) (μ : Measure Y)
    {s : Set X} : (∀ᵐ x ∂  μ.comap j,x∈s) ↔ μ (j '' sᶜ)=0 := by
  rw [ae_iff,hj.comap_apply]
  rfl

variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]

lemma weak_chart_closed (j : X → Y) (hj : Topology.IsOpenEmbedding j)
    [HasOuterApproxClosed Y] (α : ℕ → ProbabilityMeasure Y) (β : ProbabilityMeasure Y)
    (ht : Tendsto α atTop (𝓝 β)) (s : Set X) (hs : IsClosed s)
    (hα : ∀ n,(α n : Measure Y) (j '' sᶜ)=0) :
    ∀ᵐ x ∂  (β : Measure Y).comap j,x∈s := by
  rw [chart_ae_iff j hj.measurableEmbedding]
  apply le_antisymm _ zero_le
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht
    (hj.isOpenMap _ hs.isOpen_compl)).trans
  apply liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n => le_of_eq (hα n))).frequently

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

lemma map_transport {A : Type u3} {B : Type u4} {X : Type u5} {Y : Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j : A → X) (k : B → Y)
    (hj : Measurable j) (hk : MeasurableEmbedding k)
    (f : A → B) (g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure A) (ν : Measure B) (hcomm : k ∘ f=g ∘ j)
    (hm : (μ.map j).map g=ν.map k) : μ.map f=ν := by
  apply hk.map_injective
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm

lemma map_pull_ac {A : Type u7} {B : Type u8} [MeasurableSpace A] [MeasurableSpace B]
    (j : A → B) (hj : MeasurableEmbedding j) (μ ν : Measure A)
    (h : μ.map j ≪ ν.map j) : μ≪ν := by
  intro s hs
  have hν : ν.map j (j '' s)=0 := by
    rw [hj.map_apply,hj.injective.preimage_image]
    exact hs
  have hμ := h hν
  rwa [hj.map_apply,hj.injective.preimage_image] at hμ

lemma map_full_range {A : Type u9} {B : Type u10} [MeasurableSpace A] [MeasurableSpace B]
    (j : A → B) (hj : MeasurableEmbedding j) (μ : Measure A) :
    ∀ᵐ x ∂ μ.map j,x∈range j := by
  apply (ae_map_iff hj.measurable.aemeasurable hj.measurableSet_range).mpr
  exact Eventually.of_forall (fun _ => mem_range_self _)

abbrev pairCoe : ℂ × ℂ → Sphere × Sphere := Prod.map OnePoint.some OnePoint.some
abbrev quadCoe : Quad ℂ → Quad Sphere := Prod.map OnePoint.some
  (Prod.map OnePoint.some pairCoe)
abbrev expandedCoe : Expanded ℂ → Expanded Sphere := Prod.map quadCoe (Prod.map pairCoe pairCoe)

lemma pairCoe_open : Topology.IsOpenEmbedding pairCoe :=
  OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe

lemma quadCoe_open : Topology.IsOpenEmbedding quadCoe :=
  OnePoint.isOpenEmbedding_coe.prodMap (OnePoint.isOpenEmbedding_coe.prodMap pairCoe_open)

lemma expandedCoe_open : Topology.IsOpenEmbedding expandedCoe :=
  quadCoe_open.prodMap (pairCoe_open.prodMap pairCoe_open)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace WeakPinned.Bounded
open Variance
variable {V : Type u11} {I : Type u12} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

omit [Fintype I] in
lemma graph_edgeWeight_nonneg (r : I × V) :
    0≤edgeWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
  mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _)

omit [Fintype I] in
lemma graph_tripleWeight_nonneg (r : I × V × V × V) :
    0≤tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
  mul_nonneg (mul_nonneg (mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _))
    (Core.Fibers.prob_nn _ _)) (Core.Fibers.prob_nn _ _)

def edgeProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) : ProbabilityMeasure (Quad Sphere) :=
  finiteProbability (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂) (graph_edgeWeight_nonneg G)
      (sum_edgeWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))

def expandedProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) : ProbabilityMeasure (Expanded Sphere) :=
  finiteProbability (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
    (tripleValue G.source U₁ U₂) (graph_tripleWeight_nonneg G)
      (sum_tripleWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))

lemma expandedProbability_edge (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) :
    (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)).map Prod.fst=
      (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)) := by
  change (finiteLaw _ _).map _=finiteLaw _ _
  rw [finiteLaw_map _ _ _ measurable_fst]
  exact tripleLaw_edge G.fiberWeight (fun e => prob (G.targets e)) (edgeValue G.source U₁ U₂) G.fiberWeight_nonneg (fun e => Core.Fibers.prob_nn _) (fun e => sum_prob _ (hB e))

lemma edgeProbability_dom₁ (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2.1))≤
      ENNReal.ofReal (2*M) • (uniformLaw U₁).prod (uniformLaw U₁) := by
  change (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂)).map (fun q => (q.1,q.2.2.1))≤_
  rw [finiteLaw_map _ _ (fun q : Quad Sphere => (q.1,q.2.2.1)) (by fun_prop)]
  change finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e))) (fun r => (U₁ (G.source r.1),U₁ r.2))≤_
  rw [graph_edge_law G (fun x y => (U₁ x,U₁ y)) hG hB]
  exact graph_domination G U₁ hn M hM hdom

lemma edgeProbability_dom₂ (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)).map (fun q => (q.2.1,q.2.2.2))≤
      ENNReal.ofReal (2*M) • (uniformLaw U₂).prod (uniformLaw U₂) := by
  change (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂)).map (fun q => (q.2.1,q.2.2.2))≤_
  rw [finiteLaw_map _ _ (fun q : Quad Sphere => (q.2.1,q.2.2.2)) (by fun_prop)]
  change finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e))) (fun r => (U₂ (G.source r.1),U₂ r.2))≤_
  rw [graph_edge_law G (fun x y => (U₂ x,U₂ y)) hG hB]
  exact graph_domination G U₂ hn M hM hdom

end WeakPinned.Bounded

end
end

end OAI
