import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli
import OAI.Probability.CriticalPercolation.Clusters.ClusterCountFlip
import OAI.Probability.CriticalPercolation.Modular.PeakReturn
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyIdentity

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def forcedClosedSeparated (ω : Set E) (e : E) : Prop :=
  ∃ a∈G.ends e, ∃ b∈G.ends e, ¬(G.openGraph (ω\{e})).Reachable a b

def disconnectedIndicator (ω : Set E) (e : E) : ℝ :=
  if G.forcedClosedSeparated ω e then 1 else 0

lemma forcedClosedSeparated_of_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.forcedClosedSeparated ω e ↔ ¬(G.openGraph (ω\{e})).Reachable a b := by
  unfold forcedClosedSeparated
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩ hab
    rw [he,Sym2.mem_iff] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact hxy (.refl _)
    · exact hxy hab
    · exact hxy hab.symm
    · exact hxy (.refl _)
  · intro h
    exact ⟨a,by simp [he],b,by simp [he],h⟩

lemma disconnectedIndicator_of_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.disconnectedIndicator ω e=if ¬(G.openGraph (ω\{e})).Reachable a b then 1 else 0 := by
  simp only [disconnectedIndicator,G.forcedClosedSeparated_of_ends ω e a b he]

lemma measurable_forcedClosedSeparated [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.forcedClosedSeparated ω e) := by
  unfold forcedClosedSeparated
  apply Measurable.exists
  intro a
  apply measurable_const.and
  apply Measurable.exists
  intro b
  apply measurable_const.and
  exact ((G.measurable_reachable a b).comp (by
    have h := measurable_forceOn ({e}:Set E) ∅
    change Measurable (fun ω => forceOn {e} ∅ ω) at h
    simpa only [forceOn_empty_singleton] using h)).not

lemma measurable_disconnectedIndicator [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.disconnectedIndicator ω e) :=
  measurable_const.ite (G.measurable_forcedClosedSeparated e).setOf measurable_const

lemma norm_disconnectedIndicator_le (ω : Set E) (e : E) : ‖G.disconnectedIndicator ω e‖≤1 := by
  unfold disconnectedIndicator
  split_ifs <;> norm_num

lemma clusterCountDrop_eq_disconnected_of_finite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (hω : ∀ x, (G.cluster ω x).Finite) :
    G.clusterCountDrop ω e=G.disconnectedIndicator ω e := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm,
    G.disconnectedIndicator_of_ends ω e a b he.symm]
  have ha : G.modularMass a (G.cluster (ω\{e}) a)≠∞ :=
    (G.modularMass_finite a ((hω a).subset (G.cluster_mono Set.sdiff_subset a))).ne
  simp only [ha,false_and,not_false_eq_true,and_true]

lemma clusterCountDrop_le_disconnected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.clusterCountDrop ω e≤G.disconnectedIndicator ω e := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm,
    G.disconnectedIndicator_of_ends ω e a b he.symm]
  split_ifs <;> norm_num at *
  tauto

lemma finite_clusters_ae_of_subcritical [Countable V] [Countable E] (p : unitInterval)
    (hp : p<G.criticalProbability) : ∀ᵐ ω ∂G.law p, ∀ x, (G.cluster ω x).Finite := by
  have h := G.law_percolates_eq_zero_of_lt_critical hp
  have ha : ∀ᵐ ω ∂G.law p, ω∉G.percolates := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using h
  filter_upwards [ha] with ω hω x
  by_contra hf
  exact hω ⟨x,hf⟩

lemma clusterCountDrop_eq_disconnected_ae_subcritical [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (hp : p<G.criticalProbability) (e : E) :
    (fun ω => G.clusterCountDrop ω e)=ᵐ[G.law p] (fun ω => G.disconnectedIndicator ω e) := by
  filter_upwards [G.finite_clusters_ae_of_subcritical p hp] with ω hω
  exact G.clusterCountDrop_eq_disconnected_of_finite hc hl ω e hω

lemma eventually_disconnectedIndicator (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (e : E) :
    ∀ᶠ n in atTop, G.disconnectedIndicator (a n) e=G.disconnectedIndicator ω e := by
  have hmono : Monotone (fun n => a n\{e}) := fun _ _ h => Set.sdiff_subset_sdiff_left (ha h)
  have hU : (⋃ n, a n\{e})=ω\{e} := by
    rw [←Set.iUnion_sdiff,hu]
  obtain ⟨⟨x,y⟩,he⟩ := Quot.exists_rep (G.ends e)
  simp_rw [G.disconnectedIndicator_of_ends _ e x y he.symm]
  by_cases h : (G.openGraph (ω\{e})).Reachable x y
  · filter_upwards [G.eventually_cluster_of_exhaustion (fun n => a n\{e}) (ω\{e}) hmono hU h] with n hn
    change (G.openGraph (a n\{e})).Reachable x y at hn
    simp only [hn,h,not_true_eq_false,ite_false]
  · apply Eventually.of_forall
    intro n
    have hn : ¬(G.openGraph (a n\{e})).Reachable x y := fun hn => h
      (G.cluster_mono (Set.sdiff_subset_sdiff_left (hu ▸ Set.subset_iUnion a n)) x hn)
    simp only [hn,h,not_false_eq_true,ite_true]

lemma integral_atParameter [Countable V] [Countable E] (p : unitInterval)
    (f : Set E → ℝ) (hf : Measurable f) :
    (∫ u, f (atParameter p u) ∂markLaw) = ∫ ω, f ω ∂G.law p := by
  rw [←integral_map (measurable_atParameter p).aemeasurable hf.aestronglyMeasurable,
    markLaw_map_atParameter,BernoulliProduct.law_const]
  rfl

theorem tendsto_integral_disconnectedIndicator [Countable V] [Countable E]
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) (e : E) :
    Tendsto (fun n => ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) atTop
      (𝓝 (∫ ω, G.disconnectedIndicator ω e ∂G.law p)) := by
  have hm (r : unitInterval) : Measurable (fun u => G.disconnectedIndicator (atParameter r u) e) :=
    (G.measurable_disconnectedIndicator e).comp (measurable_atParameter r)
  have ht (u : E → ℝ) : Tendsto (fun n => G.disconnectedIndicator (atParameter (q n) u) e) atTop
      (𝓝 (G.disconnectedIndicator (atParameter p u) e)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (G.eventually_disconnectedIndicator (fun n => atParameter (q n) u)
      (atParameter p u) ((atParameter_mono u).comp hmono) (atParameter_iUnion p q hqp hlim u) e))
  have h := tendsto_integral_of_dominated_convergence (μ := (markLaw : Measure (E → ℝ)))
    (fun _ => (1:ℝ)) (fun n => (hm (q n)).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (fun u => G.norm_disconnectedIndicator_le _ e)) (Eventually.of_forall ht)
  simpa only [G.integral_atParameter _ _ (G.measurable_disconnectedIndicator e)] using h

end CriticalPercolation.BondGraph
end
end

end OAI
