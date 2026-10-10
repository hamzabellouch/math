import OAI.Probability.BenjaminiSchramm.ExteriorEscape
import OAI.Probability.BenjaminiSchramm.PeakSurvivalRealHeight

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakDownClusterProperty (a : V → ℝ) (ell : ℝ) (x : V) (S : Set V) : Prop :=
  (∀ y ∈ S, y ≠ x → G.orbitAdjustedHeight a x y < 0) ∧
    ∃ y ∈ S, G.orbitAdjustedHeight a x y ≤ -ell

def exteriorAvoidance (S : Set V) (a : V → ℝ) (x : V) : Set (Set E) :=
  {η | ∀ u ∈ S, η ∉ exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u}

lemma measurableSet_exteriorAvoidance [Countable V] [Countable E]
    (S : Set V) (a : V → ℝ) (x : V) : MeasurableSet (G.exteriorAvoidance S a x) :=
  (Measurable.forall fun u => measurable_const.imp
    (measurableSet_exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u).compl.mem).setOf

lemma fullPeakDownHit_iff_cluster_property (a : V → ℝ) (ell : ℝ) (x : V) (ω : Set E) :
    ω ∈ G.fullPeakDownHit a ell x ↔ G.peakDownClusterProperty a ell x (G.cluster ω x) := by
  rw [G.cluster_eq_percolationCluster]
  constructor
  · rintro ⟨⟨_,hpeak⟩,y,hy,hxy⟩
    refine ⟨fun z hz hzx => ?_,y,?_,hy⟩
    · simpa only [G.orbitAdjustedHeight_self] using hpeak z hz hzx
    · simpa only [Percolation.cluster,Set.mem_ofPred_eq,Set.inter_univ] using hxy
  · rintro ⟨hpeak,y,hxy,hy⟩
    refine ⟨⟨Percolation.conn_refl G.ends ω x,?_⟩,y,hy,?_⟩
    · intro z hz hzx
      simpa only [G.orbitAdjustedHeight_self] using hpeak z hz hzx
    · simpa only [Percolation.cluster,Set.mem_ofPred_eq,Set.inter_univ] using hxy

lemma peak_survives_white_cell (a : V → ℝ) (ell : ℝ) (x : V) (S : Set V)
    (hprop : G.peakDownClusterProperty a ell x S) (ω : Set (E × Bool))
    (hS : G.cluster (whiteProjection ω) x=S)
    (havoid : pairedUnion (forceOn (whiteBlock (G.incidentEdges S)) ∅ ω) ∈ G.exteriorAvoidance S a x) :
    pairedUnion ω ∈ G.fullPeakDownHit a ell x := by
  have hwhite : whiteProjection ω ∈ G.fullPeakDownHit a ell x :=
    (G.fullPeakDownHit_iff_cluster_property a ell x _).mpr (hS ▸ hprop)
  have hSc : Percolation.cluster G.ends (whiteProjection ω) x=S := by
    rwa [←G.cluster_eq_percolationCluster]
  have hη : pairedUnion (forceOn (whiteBlock (G.incidentEdges S)) ∅ ω) \
      Percolation.internalEdges G.ends S=pairedUnion ω \ Percolation.internalEdges G.ends S := by
    have hh := G.erasedWhiteCluster_exterior_eq ω x
    rwa [hS] at hh
  have hpeak : ∀ y, Percolation.Conn G.ends (pairedUnion ω) x y → y ≠ x →
      G.orbitAdjustedHeight a x y < G.orbitAdjustedHeight a x x := by
    rw [pairedUnion_eq]
    apply union_strict_peak_of_exterior_avoidance G.ends (whiteProjection ω) (blueProjection ω)
      (G.orbitAdjustedHeight a x) x hwhite.1.2
    intro u hu hescape
    have huS : u ∈ S := hSc ▸ hu
    apply havoid u huS
    rcases hescape with ⟨y,hy,hheight,hyS,hconn⟩
    refine ⟨y,hy,hheight,?_,?_⟩
    · rwa [hSc] at hyS
    · rw [hη,pairedUnion_eq,←hSc]
      exact hconn
  refine ⟨⟨Percolation.conn_refl G.ends _ x,hpeak⟩,?_⟩
  obtain ⟨y,hy,hxy⟩ := hwhite.2
  refine ⟨y,hy,?_⟩
  apply Percolation.conn_mono G.ends _ hxy
  intro e he
  exact ⟨(pairedUnion_eq ω).symm ▸ Or.inl he.1,he.2⟩

variable [Countable V] [Countable E]

theorem peak_sprinkling_cell_lower (q b : unitInterval) (a : V → ℝ)
    (x : V) (S : Finset V)
    (g : V → ℝ)
    (hbound : ∀ u ∈ S, Real.exp (-g u) ≤
      (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
        (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
          (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ) :
    G.law q {η | G.cluster η x=(S : Set V)} *
      ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g u))) ≤
      BernoulliProduct.law (pairedParameters (fun _ => q) (fun _ => b))
        ({ω | G.cluster (whiteProjection ω) x=(S : Set V)} ∩
          (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
            G.exteriorAvoidance (S : Set V) a x) := by
  rw [fresh_white_union_event_factor (fun _ => q) (fun _ => b)
    (G.incidentEdges (S : Set V)) {ω | G.cluster (whiteProjection ω) x=(S : Set V)}
    ((G.measurableSet_exactCluster x _).preimage measurable_whiteProjection)
    (G.paired_exactWhiteCluster_dependsOn x _) (G.exteriorAvoidance (S : Set V) a x)
    (G.measurableSet_exteriorAvoidance _ a x)]
  have hcell : BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
      {ω | G.cluster (whiteProjection ω) x=(S : Set V)}=
      G.law q {η | G.cluster η x=(S : Set V)} := by
    change BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
      (whiteProjection ⁻¹' {η | G.cluster η x=(S : Set V)})=_
    rw [←Measure.map_apply measurable_whiteProjection (G.measurableSet_exactCluster x _),
      paired_white_law,BernoulliProduct.law_const]
    rfl
  rw [hcell]
  exact mul_le_mul' le_rfl (exteriorEscape_avoidance_product G.ends _ S
    (G.orbitAdjustedHeight a x) x g hbound)

end CriticalPercolation.BondGraph

end

end OAI
