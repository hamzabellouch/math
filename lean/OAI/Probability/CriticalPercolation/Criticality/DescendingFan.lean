import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.Modular.HeavyHarris

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def weightCeiling (v : V) (K : ℝ≥0∞) : Set V := {x | G.stabilizerWeight v x≤K}

def descendingFanEvent (v : V) (K ε : ℝ≥0∞) (N : ℕ) : Set (Set E) :=
  {ω | ∃ S : Finset V, N≤S.card ∧ ∀ x∈S,
    x∈G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v ∧
      G.stabilizerWeight v x<ε}

lemma descendingFanEvent_upper (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    IsUpperSet (G.descendingFanEvent v K ε N) := by
  rintro ω η h ⟨S,hS,hs⟩
  exact ⟨S,hS,fun x hx => ⟨G.cluster_mono (Set.inter_subset_inter_left _ h) v
    (hs x hx).1,(hs x hx).2⟩⟩

lemma descendingFanEvent_finiteWitness (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.descendingFanEvent v K ε N) := by
  rintro ω ⟨S,hS,hs⟩
  obtain ⟨J,hJ,hJω,hconn⟩ := G.finite_subset_cluster_finite_witness S.finite_toSet
    (show (S : Set V)⊆G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v from
      fun x hx => (hs x hx).1)
  refine ⟨J,hJ,hJω.trans Set.inter_subset_left,S,hS,?_⟩
  intro x hx
  refine ⟨?_,(hs x hx).2⟩
  have he : J∩G.inducedEdges (G.weightCeiling v K)=J :=
    Set.inter_eq_left.mpr (hJω.trans Set.inter_subset_right)
  rw [he]
  exact hconn hx

lemma measurableSet_descendingFanEvent [Countable E] (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    MeasurableSet (G.descendingFanEvent v K ε N) :=
  BernoulliProduct.measurableSet_finiteWitness _ (G.descendingFanEvent_upper v K ε N)
    (G.descendingFanEvent_finiteWitness v K ε N)

lemma stabilizerWeight_le_modularMass {S : Set V} {v x : V} (hx : x∈S) :
    G.stabilizerWeight v x≤G.modularMass v S := by
  simpa only [ite_eq_left hx,modularMass] using
    (ENNReal.le_tsum x (f := fun y => if y∈S then G.stabilizerWeight v y else 0))

lemma finite_mass_low_slice_infinite {S : Set V} {v : V}
    (hi : S.Infinite) (hm : G.modularMass v S≠∞) (ε : ℝ≥0∞) (hε : 0<ε) :
    (S∩{x | G.stabilizerWeight v x<ε}).Infinite := by
  have hf : (S∩{x | ε≤G.stabilizerWeight v x}).Finite := by
    apply (ENNReal.finite_const_le_of_tsum_ne_top hm hε.ne').subset
    intro x hx
    change ε ≤ if x∈S then G.stabilizerWeight v x else 0
    rw [ite_eq_left hx.1]
    exact hx.2
  have hh := hi.sdiff hf
  apply hh.mono
  intro x hx
  refine ⟨hx.1,?_⟩
  change G.stabilizerWeight v x<ε
  apply lt_of_not_ge
  intro he
  exact hx.2 ⟨hx.1,he⟩

lemma cluster_eq_with_weightCeiling {ω : Set E} {v : V} {K : ℝ≥0∞}
    (hK : G.modularMass v (G.cluster ω v)≤K) :
    G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v=G.cluster ω v := by
  apply Set.Subset.antisymm (G.cluster_mono Set.inter_subset_left v)
  rintro x ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro y hy
  exact (G.stabilizerWeight_le_modularMass (w.takeUntil y hy).reachable).trans hK

lemma bounded_mass_infinite_subset_fan (v : V) (K ε : ℝ≥0∞) (hK : K≠∞)
    (hε : 0<ε) (N : ℕ) :
    G.infiniteEvent v \ G.massTailEvent v v K ⊆ G.descendingFanEvent v K ε N := by
  rintro ω ⟨hi,hm⟩
  have hm' : G.modularMass v (G.cluster ω v)≤K := le_of_not_gt hm
  have hh := G.finite_mass_low_slice_infinite hi (ne_top_of_le_ne_top hK hm') ε hε
  obtain ⟨S,hS,hcard⟩ := hh.exists_subset_card_eq N
  refine ⟨S,hcard.ge,fun x hx => ?_⟩
  have hs := hS hx
  rw [G.cluster_eq_with_weightCeiling hm']
  exact hs

lemma Aut.weightCeiling_image (φ : G.Aut) (v : V) (K : ℝ≥0∞) :
    φ.vertex '' G.weightCeiling v K=G.weightCeiling (φ.vertex v) K := by
  ext x
  obtain ⟨y,rfl⟩ := φ.vertex.surjective x
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,weightCeiling,
    Set.mem_ofPred_eq,φ.stabilizerWeight]

lemma Aut.image_inducedEdges (φ : G.Aut) (S : Set V) :
    φ.edge '' G.inducedEdges S=G.inducedEdges (φ.vertex '' S) := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,inducedEdges,
    Set.mem_ofPred_eq,φ.preserves,Sym2.mem_map]
  constructor
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,h y hy,rfl⟩
  · intro h y hy
    obtain ⟨z,hz,he⟩ := h (φ.vertex y) ⟨y,hy,rfl⟩
    exact (φ.vertex.injective he) ▸ hz

lemma Aut.descendingFanEvent_preimage (φ : G.Aut) (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.descendingFanEvent (φ.vertex v) K ε N=
      G.descendingFanEvent v K ε N := by
  have he (ω : Set E) :
      (φ.edge '' ω)∩G.inducedEdges (G.weightCeiling (φ.vertex v) K)=
        φ.edge '' (ω∩G.inducedEdges (G.weightCeiling v K)) := by
    rw [Set.image_inter φ.edge.injective,φ.image_inducedEdges,φ.weightCeiling_image]
  have hr (ω : Set E) (x : V) :
      φ.vertex x∈G.cluster ((φ.edge '' ω)∩G.inducedEdges (G.weightCeiling (φ.vertex v) K))
        (φ.vertex v) ↔ x∈G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v := by
    rw [he]
    exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ _))
  ext ω
  constructor
  · rintro ⟨S,hS,hs⟩
    refine ⟨S.image φ.vertex.symm,?_,?_⟩
    · rwa [Finset.card_image_of_injective _ φ.vertex.symm.injective]
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have h := hs y hy
      refine ⟨(hr ω (φ.vertex.symm y)).mp (by simpa using h.1),?_⟩
      simpa only [←Aut.stabilizerWeight G φ v (φ.vertex.symm y),φ.vertex.apply_symm_apply] using h.2
  · rintro ⟨S,hS,hs⟩
    refine ⟨S.image φ.vertex,?_,?_⟩
    · rwa [Finset.card_image_of_injective _ φ.vertex.injective]
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨(hr ω y).mpr (hs y hy).1,by simpa only [φ.stabilizerWeight] using (hs y hy).2⟩

lemma Aut.descendingFanEvent_real [Countable E] (φ : G.Aut) (p : unitInterval)
    (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    (G.law p).real (G.descendingFanEvent (φ.vertex v) K ε N)=
      (G.law p).real (G.descendingFanEvent v K ε N) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_descendingFanEvent _ _ _ _),φ.descendingFanEvent_preimage]

end CriticalPercolation.BondGraph
end
end

end OAI
