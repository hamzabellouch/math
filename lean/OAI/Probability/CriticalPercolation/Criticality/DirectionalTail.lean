import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct
import OAI.Probability.CriticalPercolation.Clusters.InfiniteUniqueness
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteEventSubsetHit

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infiniteVertices (ω : Set E) : Set V := {v | (G.cluster ω v).Infinite}

lemma infiniteVertices_mono {ω τ : Set E} (h : ω⊆τ) :
    G.infiniteVertices ω⊆G.infiniteVertices τ := fun v hv => hv.mono (G.cluster_mono h v)

lemma cluster_union_unchanged (ω S : Set E) (o : V)
    (hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω o) :
    G.cluster (ω∪S) o=G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro z hz
    have hr := ((G.openGraph (ω∪S)).reachable_iff_reflTransGen o z).mp hz
    clear hz
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases he with he|he
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hend⟩,hne⟩
        exact ih.trans hadj.reachable
      · exact False.elim (hends e he x (by simp [hend]) ih)
  · exact G.cluster_mono Set.subset_union_left o

lemma infiniteVertices_union_finite_error (ω S : Set E) (hS : S.Finite) :
    (G.infiniteVertices (ω∪S)\G.infiniteVertices ω).Finite := by
  let K := ⋃ e∈S, ⋃ v∈(G.ends e).toFinset,
    {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}
  have hK : K.Finite := hS.biUnion fun e _ => (G.ends e).toFinset.finite_toSet.biUnion fun v _ => by
    by_cases hv : (G.cluster ω v).Finite
    · exact hv.subset (fun _ h => h.1)
    · have heq : {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}=(∅ : Set V) := by
        ext x
        simp [hv]
      rw [heq]
      exact Set.finite_empty
  apply hK.subset
  intro x hx
  have hfin : (G.cluster ω x).Finite := Set.not_infinite.mp hx.2
  by_contra hn
  have hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω x := by
    intro e he v hv hvc
    apply hn
    refine Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,?_,hvc.symm,?_⟩⟩
    · simpa only [Sym2.mem_toFinset] using hv
    · rwa [← G.cluster_eq_of_reachable hvc]
  exact hx.1 (by rwa [G.cluster_union_unchanged ω S x hends])

def directionUnbounded (f : V → ℝ) : Set (Set E) :=
  {ω | ∀ n : ℕ, ∃ v, (n : ℝ)<f v ∧ v∈G.infiniteVertices ω}

lemma directionUnbounded_mono (f : V → ℝ) : IsUpperSet (G.directionUnbounded f) := by
  intro ω τ h hω n
  obtain ⟨v,hv,hv'⟩ := hω n
  exact ⟨v,hv,G.infiniteVertices_mono h hv'⟩

lemma directionUnbounded_union_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω∪S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · intro h n
    have hK := (G.infiniteVertices_union_finite_error ω S hS).image f
    obtain ⟨M,hM⟩ := hK.bddAbove
    obtain ⟨N,hN⟩ := exists_nat_gt (max M n)
    obtain ⟨v,hv,hinf⟩ := h N
    refine ⟨v,lt_trans (lt_of_le_of_lt (le_max_right M n) hN) hv,?_⟩
    by_contra hnot
    have hfM := hM (Set.mem_image_of_mem f ⟨hinf,hnot⟩)
    have : M<(N : ℝ) := lt_of_le_of_lt (le_max_left M n) hN
    linarith
  · exact G.directionUnbounded_mono f Set.subset_union_left

lemma directionUnbounded_diff_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · exact G.directionUnbounded_mono f Set.sdiff_subset
  · intro h
    have hs : ω⊆(ω\S)∪S := fun e he => by
      by_cases hh : e∈S
      · exact Or.inr hh
      · exact Or.inl ⟨he,hh⟩
    exact (G.directionUnbounded_union_finite_iff f (ω\S) S hS).mp
      (G.directionUnbounded_mono f hs h)

lemma directionUnbounded_measurable [Countable V] [Countable E] (f : V → ℝ) :
    MeasurableSet (G.directionUnbounded f) := by
  have heq : G.directionUnbounded f=⋂ n : ℕ, ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v := by
    ext ω
    simp only [directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    G.measurableSet_infiniteEvent v

lemma directionUnbounded_zero_one [Countable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) :
    BernoulliProduct.law q (G.directionUnbounded f)=0 ∨
      BernoulliProduct.law q (G.directionUnbounded f)=1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q _ (G.directionUnbounded_measurable f)
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  exact G.directionUnbounded_diff_finite_iff f ω S hS

lemma directionUnbounded_positive [Countable V] [Countable E]
    (p : unitInterval) (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v)
    (theta : ℝ) (htheta : 0<theta)
    (hroot : ∀ v, theta≤(G.law p).real (G.infiniteEvent v)) :
    0<G.law p (G.directionUnbounded f) := by
  let A := fun n : ℕ => ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun v _ => G.measurableSet_infiniteEvent v
  have hanti : Antitone A := by
    intro n m hnm ω hω
    obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨v,(show (n : ℝ)<f v from lt_of_le_of_lt (Nat.cast_le.mpr hnm) hv),hh⟩
  have heq : (⋂ n, A n)=G.directionUnbounded f := by
    ext ω
    simp only [A,directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  have ht := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
  rw [heq] at ht
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hbound : ∀ n, theta≤(G.law p).real (A n) := by
    intro n
    obtain ⟨v,hv⟩ := hf n
    have hs : G.infiniteEvent v⊆A n := fun ω hω => Set.mem_iUnion₂.mpr ⟨v,hv,hω⟩
    exact (hroot v).trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs))
  have hp : 0<(G.law p).real (G.directionUnbounded f) :=
    htheta.trans_le (ge_of_tendsto hreal (Eventually.of_forall hbound))
  exact ENNReal.toReal_pos_iff.mp hp |>.1

theorem directionUnbounded_one [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    G.law p (G.directionUnbounded f)=1 := by
  obtain ⟨theta,htheta,hroot⟩ := G.uniform_rooted_probability hc hl hq p hpositive
  have hp := G.directionUnbounded_positive p f hf theta htheta hroot
  have hz := G.directionUnbounded_zero_one (fun _ => p) f
  rw [BernoulliProduct.law_const] at hz
  exact hz.resolve_left (ne_of_gt hp)

theorem unique_cluster_direction_unbounded_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
      ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w := by
  have hu : ∀ᵐ ω ∂G.law p, ω∈G.directionUnbounded f := by
    rw [ae_iff]
    change G.law p (G.directionUnbounded f)ᶜ=0
    rw [measure_compl (G.directionUnbounded_measurable f) (measure_ne_top _ _),
      G.directionUnbounded_one hc hl hq p hpositive f hf,measure_univ,tsub_self]
  filter_upwards [hu,G.atMostOneInfinite_ae hc hl hq hg p hp] with ω hω huniq
  intro v hv n
  obtain ⟨w,hw,hwinf⟩ := hω n
  exact ⟨w,huniq v w hv hwinf,hw⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
