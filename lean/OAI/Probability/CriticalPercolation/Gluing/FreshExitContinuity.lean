import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.OpenFrontierDivergence
import OAI.Probability.CriticalPercolation.Gluing.FreshExitWitness
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
variable {v : V}

omit [Countable V] [Countable E] in
lemma infinite_sdiff_freshExit_bound (hl : G.LocallyFinite) (p : unitInterval)
    (S : Set V) (v : V) (N : ℕ)
    (hf : ∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges S) v).Finite) :
    G.law p (G.infiniteEvent v\G.freshExitEvent S v N)≤
      G.law p (G.infiniteEvent v∩G.fewOpenFreshBoundary (G.inducedEdges S) v N) := by
  apply measure_mono_ae
  filter_upwards [hf] with ω hω
  rintro ⟨hi,hn⟩
  refine ⟨hi,hω,?_⟩
  by_contra h
  apply hn
  exact G.freshExitEvent_of_card S v N ω
    (((G.finite_cutEdges hl hω).subset Set.sdiff_subset).inter_of_left ω)
    (Nat.le_of_lt (Nat.lt_of_not_ge h))

theorem freshExit_failure_tendsto_zero (hl : G.LocallyFinite)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (S : ℕ → Set V)
    (hex : ∀ F : Finset E, ∀ᶠ n in atTop, (F : Set E)⊆G.inducedEdges (S n))
    (hf : ∀ n, ∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges (S n)) v).Finite)
    (N : ℕ) :
    Tendsto (fun n => G.law p (G.infiniteEvent v\G.freshExitEvent (S n) v N))
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (G.fewOpenFreshBoundary_probability_tendsto_zero hl p hp hp1
      (fun n => G.inducedEdges (S n)) hex v N)
    (Eventually.of_forall (fun _ => zero_le))
    (Eventually.of_forall (fun n => G.infinite_sdiff_freshExit_bound hl p (S n) v N (hf n)))

lemma freshExit_eventually_large (hl : G.LocallyFinite)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (S : ℕ → Set V)
    (hex : ∀ F : Finset E, ∀ᶠ n in atTop, (F : Set E)⊆G.inducedEdges (S n))
    (hf : ∀ n, ∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges (S n)) v).Finite)
    (N : ℕ) (θ : ℝ) (hθ : θ<(G.law p).real (G.infiniteEvent v)) :
    ∀ᶠ n in atTop, θ<(G.law p).real (G.freshExitEvent (S n) v N) := by
  have ht := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (G.freshExit_failure_tendsto_zero hl p hp hp1 S hex hf N)
  simp only [ENNReal.toReal_zero,Function.comp_def] at ht
  have hε : 0<(G.law p).real (G.infiniteEvent v)-θ := sub_pos.mpr hθ
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  have hcover : G.infiniteEvent v⊆
      (G.infiniteEvent v\G.freshExitEvent (S n) v N)∪G.freshExitEvent (S n) v N := by
    intro ω hω
    by_cases h : ω∈G.freshExitEvent (S n) v N
    · exact Or.inr h
    · exact Or.inl ⟨hω,h⟩
  have hb := (measureReal_mono hcover (μ := G.law p)).trans (measureReal_union_le _ _)
  change (G.law p).real (G.infiniteEvent v\G.freshExitEvent (S n) v N)<_ at hn
  linarith

theorem exists_freshExit_lower_parameter (hl : G.LocallyFinite)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (S : ℕ → Set V) (hv : ∀ n, v∈S n)
    (hex : ∀ F : Finset E, ∀ᶠ n in atTop, (F : Set E)⊆G.inducedEdges (S n))
    (hf : ∀ n, ∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges (S n)) v).Finite)
    (N : ℕ) (θ : ℝ) (hθ : θ<(G.law p).real (G.infiniteEvent v)) :
    ∃ n, ∃ q : unitInterval, (p:ℝ)/2≤q ∧ q<p ∧
      θ<(G.law q).real (G.freshExitEvent (S n) v N) := by
  obtain ⟨n,hn⟩ := (G.freshExit_eventually_large hl p hp hp1 S hex hf N θ hθ).exists
  obtain ⟨q,hhalf,hqp,hq⟩ := BernoulliProduct.exists_lower_parameter
    (I := Unit) (fun _ => G.freshExitEvent (S n) v N)
    (fun _ => G.freshExitEvent_upper (hv n) N)
    (fun _ => G.freshExitEvent_finiteWitness (hv n) N) p hp
    (fun _ => θ) (fun _ => by simpa only [BernoulliProduct.law_const,law] using hn)
  exact ⟨n,q,hhalf,hqp,by simpa only [BernoulliProduct.law_const,law] using hq ()⟩

end CriticalPercolation.BondGraph
end
end

end OAI
