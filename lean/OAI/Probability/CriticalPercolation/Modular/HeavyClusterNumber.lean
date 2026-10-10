import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.FiniteClusterCover
import OAI.Probability.CriticalPercolation.Clusters.GraphErgodicity
import OAI.Probability.CriticalPercolation.Clusters.PercolationTail
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_union_le (o : V) (S T : Set V) :
    G.modularMass o (S ∪ T) ≤ G.modularMass o S + G.modularMass o T := by
  unfold modularMass
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hs : x∈S <;> by_cases ht : x∈T <;> simp [hs,ht]

lemma modularMass_finite_biUnion_lt_top {ι : Type*} (o : V) (I : Set ι)
    (hI : I.Finite) (S : ι → Set V) (hS : ∀ i∈I, G.modularMass o (S i) < ∞) :
    G.modularMass o (⋃ i∈I, S i) < ∞ := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp [modularMass]
  | @insert i I hi hI ih =>
    rw [Set.biUnion_insert]
    apply lt_of_le_of_lt (G.modularMass_union_le o _ _)
    exact ENNReal.add_lt_top.mpr ⟨hS i (by simp),ih (fun j hj => hS j (by simp [hj]))⟩

lemma heavy_cluster_union_has_old (ω J : Set E) (hJ : J.Finite) (o x : V)
    (hx : G.modularMass o (G.cluster (ω ∪ J) x) = ∞) :
    ∃ v, (G.openGraph (ω ∪ J)).Reachable x v ∧ G.modularMass o (G.cluster ω v) = ∞ := by
  by_contra h
  have hf (v : V) (hv : (G.openGraph (ω ∪ J)).Reachable x v) :
      G.modularMass o (G.cluster ω v) < ∞ := by
    exact lt_top_iff_ne_top.mpr (fun hi => h ⟨v,hv,hi⟩)
  have hσ (v : V) : G.modularMass o (G.cluster ω v ∩ G.cluster (ω ∪ J) x) < ∞ := by
    by_cases hv : (G.openGraph (ω ∪ J)).Reachable x v
    · exact lt_of_le_of_lt (G.modularMass_mono o Set.inter_subset_left) (hf v hv)
    · have he : G.cluster ω v ∩ G.cluster (ω ∪ J) x = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨hz,hxz⟩
        exact hv (hxz.trans (G.cluster_mono Set.subset_union_left v hz).symm)
      simp [he,modularMass]
  have hsub : G.cluster (ω ∪ J) x ⊆ G.cluster ω x ∪
      ⋃ e∈J, ⋃ v∈(G.ends e).toFinset, G.cluster ω v ∩ G.cluster (ω ∪ J) x := by
    intro z hz
    rcases G.cluster_union_subset ω J x hz with hh | hh
    · exact Or.inl hh
    · obtain ⟨e,he,hh⟩ := Set.mem_iUnion₂.mp hh
      obtain ⟨v,hv,hvz⟩ := Set.mem_iUnion₂.mp hh
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,hv,hvz,hz⟩⟩)
  have hb : G.modularMass o (G.cluster (ω ∪ J) x) < ∞ := by
    apply lt_of_le_of_lt (G.modularMass_mono o hsub)
    apply lt_of_le_of_lt (G.modularMass_union_le o _ _)
    apply ENNReal.add_lt_top.mpr
    refine ⟨hf x (.refl _),?_⟩
    apply G.modularMass_finite_biUnion_lt_top o J hJ
    intro e _
    exact G.modularMass_finite_biUnion_lt_top o _ (G.ends e).toFinset.finite_toSet _ (fun v _ => hσ v)
  exact (ne_of_lt hb) hx

def atMostOneHeavy (o : V) : Set (Set E) :=
  {ω | ∀ x y, G.modularMass o (G.cluster ω x) = ∞ →
    G.modularMass o (G.cluster ω y) = ∞ → (G.openGraph ω).Reachable x y}

def heavyClusterCover (o : V) (ω : Set E) (S : Set V) : Prop :=
  ∀ v, G.modularMass o (G.cluster ω v) = ∞ → ∃ s∈S, (G.openGraph ω).Reachable v s

def infinitelyManyHeavyClusters (o : V) (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, G.modularMass o (G.cluster ω v) = ∞ ∧
    ∀ s∈S, ¬(G.openGraph ω).Reachable v s

lemma measurableSet_atMostOneHeavy [Countable V] [Countable E] (o : V) :
    MeasurableSet (G.atMostOneHeavy o) := by
  apply Measurable.setOf
  exact .forall fun x => .forall fun y =>
    ((G.measurable_modularClusterMass o x).eq_const ∞).imp
      (((G.measurable_modularClusterMass o y).eq_const ∞).imp (G.measurable_reachable x y))

lemma measurable_heavyClusterCover [Countable V] [Countable E] (o : V) (S : Set V) :
    Measurable (fun ω => G.heavyClusterCover o ω S) := by
  exact .forall fun v => ((G.measurable_modularClusterMass o v).eq_const ∞).imp
    (.exists fun s => measurable_const.and (G.measurable_reachable v s))

lemma infinitelyManyHeavyClusters_iff_no_finite_cover (o : V) (ω : Set E) :
    G.infinitelyManyHeavyClusters o ω ↔ ∀ S : Finset V, ¬G.heavyClusterCover o ω (S : Set V) := by
  simp only [infinitelyManyHeavyClusters,heavyClusterCover]
  push Not
  rfl

lemma measurable_infinitelyManyHeavyClusters [Countable V] [Countable E] (o : V) :
    Measurable (fun ω => G.infinitelyManyHeavyClusters o ω) := by
  simp_rw [G.infinitelyManyHeavyClusters_iff_no_finite_cover]
  exact .forall fun S => (G.measurable_heavyClusterCover o (S : Set V)).not

lemma Aut.atMostOneHeavy_image_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (o : V) (ω : Set E) :
    φ.edge '' ω ∈ G.atMostOneHeavy o ↔ ω ∈ G.atMostOneHeavy o := by
  have hi (x : V) : G.modularMass o (G.cluster (φ.edge '' ω) (φ.vertex x)) = ∞ ↔
      G.modularMass o (G.cluster ω x) = ∞ := by
    rw [G.modularMass_eq_top_change_base hc hl o (φ.vertex o),←φ.cluster_image,φ.modularMass_image]
  have hr (x y : V) := SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := x) (v := y)
  constructor
  · intro h x y hx hy
    exact (hr x y).mp (h (φ.vertex x) (φ.vertex y) ((hi x).mpr hx) ((hi y).mpr hy))
  · intro h x y hx hy
    obtain ⟨a,rfl⟩ := φ.vertex.surjective x
    obtain ⟨b,rfl⟩ := φ.vertex.surjective y
    exact (hr a b).mpr (h a b ((hi a).mp hx) ((hi b).mp hy))

lemma atMostOneHeavy_union_of_cover (ω J : Set E) (hJ : J.Finite)
    (o x : V) (S : Set V) (hconn : ∀ s∈S, (G.openGraph J).Reachable x s)
    (hcover : G.heavyClusterCover o ω S) : ω ∪ J ∈ G.atMostOneHeavy o := by
  have hroot (y : V) (hy : G.modularMass o (G.cluster (ω ∪ J) y) = ∞) :
      (G.openGraph (ω ∪ J)).Reachable y x := by
    obtain ⟨v,hyv,hv⟩ := G.heavy_cluster_union_has_old ω J hJ o y hy
    obtain ⟨s,hs,hvs⟩ := hcover v hv
    exact hyv.trans ((G.cluster_mono Set.subset_union_left v hvs).trans
      (G.cluster_mono Set.subset_union_right x (hconn s hs)).symm)
  exact fun a b ha hb => (hroot a ha).trans (hroot b hb).symm

lemma no_finite_heavyClusterCover_ae_of_unique_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : (0:ℝ)<p) (o : V)
    (hnull : G.law p (G.atMostOneHeavy o) = 0) :
    ∀ᵐ ω ∂G.law p, ∀ S : Finset V, ¬G.heavyClusterCover o ω (S : Set V) := by
  apply ae_all_iff.mpr
  intro S
  obtain ⟨J,hJ,hconn⟩ := G.finite_bonds_connect_set hc o (S : Set V) S.finite_toSet
  have hn := BernoulliProduct.finite_union_preimage_null (fun _ : E => p) (fun _ => hp)
    J hJ (G.atMostOneHeavy o) (G.measurableSet_atMostOneHeavy o)
    (by simpa only [BernoulliProduct.law_const,law] using hnull)
  have hn' : G.law p ((fun ω : Set E => J ∪ ω) ⁻¹' G.atMostOneHeavy o) = 0 := by
    simpa only [BernoulliProduct.law_const,law] using hn
  rw [ae_iff]
  apply measure_mono_null _ hn'
  intro ω hω
  change J ∪ ω ∈ G.atMostOneHeavy o
  rw [Set.union_comm]
  exact G.atMostOneHeavy_union_of_cover ω J hJ o o (S : Set V) hconn (not_not.mp hω)

theorem unique_heavy_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : (0:ℝ)<p) (o : V) :
    (∀ᵐ ω ∂G.law p, ω∈G.atMostOneHeavy o) ∨
      (∀ᵐ ω ∂G.law p, G.infinitelyManyHeavyClusters o ω) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  rcases G.invariant_event_zero_one hc hl hq p (G.atMostOneHeavy o)
    (G.measurableSet_atMostOneHeavy o)
    (fun φ => Set.ext fun ω => Aut.atMostOneHeavy_image_iff G hc hl φ o ω) with hz | ho
  · right
    filter_upwards [G.no_finite_heavyClusterCover_ae_of_unique_null hc p hp o hz] with ω hω
    exact (G.infinitelyManyHeavyClusters_iff_no_finite_cover o ω).mpr hω
  · left
    rw [ae_iff]
    change G.law p (G.atMostOneHeavy o)ᶜ = 0
    rw [measure_compl (G.measurableSet_atMostOneHeavy o) (measure_ne_top _ _),ho,
      measure_univ,tsub_self]

end CriticalPercolation.BondGraph
end
end

end OAI
