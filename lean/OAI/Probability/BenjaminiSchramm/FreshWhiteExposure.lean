import OAI.Probability.BenjaminiSchramm.PairedSprinkling
import OAI.Probability.BenjaminiSchramm.BlockExposure
import OAI.Probability.BenjaminiSchramm.ClusterExposure
import OAI.Probability.BenjaminiSchramm.SprinklingPeakGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma fresh_white_union_inter_factor (q b : E → unitInterval) (Q : Set E)
    (A B : Set (Set (E × Bool))) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) (whiteBlock Q)) (hB : MeasurableSet B) :
    law (pairedParameters q b) (A ∩ forceOn (whiteBlock Q) ∅ ⁻¹' B)=
      law (pairedParameters q b) A *
        law (pairedParameters (erasedWhiteParameters q Q) b) B := by
  let g := fun ω => B.indicator (fun _ => (1 : ℝ≥0∞)) (forceOn (whiteBlock Q) ∅ ω)
  have hg : Measurable g := (measurable_const.indicator hB).comp (measurable_forceOn _ _)
  have hgd : DependsOn g (whiteBlock Q)ᶜ := by
    intro ω η hωη
    have hh : forceOn (whiteBlock Q) ∅ ω=forceOn (whiteBlock Q) ∅ η := by
      ext z
      change (if z ∈ whiteBlock Q then False else ω z) ↔
        (if z ∈ whiteBlock Q then False else η z)
      by_cases hz : z ∈ whiteBlock Q
      · simp only [ite_eq_left hz]
      · simpa only [ite_eq_right hz] using (hωη z hz).to_iff
    exact congrArg (B.indicator (fun _ => (1 : ℝ≥0∞))) hh
  have hi := lintegral_indicator_fresh (pairedParameters q b) (whiteBlock Q) A hA hdep g hg hgd
  have he : A.indicator g=(A ∩ forceOn (whiteBlock Q) ∅ ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : forceOn (whiteBlock Q) ∅ ω ∈ B <;>
      simp [Set.indicator,g,ha,hb]
  have hmB := hB.preimage (measurable_forceOn (whiteBlock Q) ∅)
  rw [he,lintegral_indicator_fun_one (hA.inter hmB)] at hi
  have hgint : (∫⁻ ω, g ω ∂law (pairedParameters q b))=
      law (pairedParameters (erasedWhiteParameters q Q) b) B := by
    change (∫⁻ ω, (forceOn (whiteBlock Q) ∅ ⁻¹' B).indicator
      (fun _ => (1 : ℝ≥0∞)) ω ∂law (pairedParameters q b))=_
    rw [lintegral_indicator_fun_one hmB,←Measure.map_apply (measurable_forceOn _ _) hB,
      forceOn_map_law,pinned_white_parameters]
  rwa [hgint] at hi

lemma fresh_white_union_event_factor (q b : E → unitInterval) (Q : Set E)
    (A : Set (Set (E × Bool))) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) (whiteBlock Q))
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law (pairedParameters q b)
      (A ∩ (pairedUnion ∘ forceOn (whiteBlock Q) ∅) ⁻¹' B)=
      law (pairedParameters q b) A *
        law (fun e => Percolation.sprinkleParameter (erasedWhiteParameters q Q e) (b e)) B := by
  rw [show (pairedUnion ∘ forceOn (whiteBlock Q) ∅) ⁻¹' B=
    forceOn (whiteBlock Q) ∅ ⁻¹' (pairedUnion ⁻¹' B) from rfl]
  rw [fresh_white_union_inter_factor q b Q A _ hA hdep (hB.preimage measurable_pairedUnion),
    ←Measure.map_apply measurable_pairedUnion hB,paired_union_law]

lemma erased_pairedUnion (Q : Set E) (ω : Set (E × Bool)) :
    pairedUnion (forceOn (whiteBlock Q) ∅ ω)=
      (whiteProjection ω \ Q) ∪ blueProjection ω := by
  ext e
  by_cases he : e ∈ Q <;>
    simp [pairedUnion,whiteBlock,whiteProjection,blueProjection,
      Bool.exists_bool,he,and_comm,or_comm]

end CriticalPercolation.BernoulliProduct

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_eq_percolationCluster (ω : Set E) (x : V) :
    G.cluster ω x=Percolation.cluster G.ends ω x := criticalModel_cluster G.ends ω x

lemma paired_exactWhiteCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set (E × Bool) => G.cluster (whiteProjection ω) x=S)
      (whiteBlock (G.incidentEdges S)) := by
  intro ω η hωη
  apply G.exactCluster_dependsOn x S
  intro e he
  exact hωη (e,true) ⟨he,rfl⟩

lemma white_edge_incident_cluster_internal (white : Set E) (x : V) (e : E)
    (he : e ∈ white) (hI : e ∈ G.incidentEdges (G.cluster white x)) :
    e ∈ Percolation.internalEdges G.ends (G.cluster white x) := by
  have hS : G.cluster white x=Percolation.cluster G.ends white x := criticalModel_cluster G.ends white x
  rw [hS] at hI ⊢
  obtain ⟨v,hv,hve⟩ := hI
  intro w hw
  by_cases h : v=w
  · simpa only [←h] using hv
  · have heq : G.ends e=s(v,w) := (Sym2.mem_and_mem_iff h).mp ⟨hve,hw⟩
    exact hv.trans (Relation.ReflTransGen.single ⟨e,he,heq⟩)

lemma erasedWhiteCluster_exterior_eq (ω : Set (E × Bool)) (x : V) :
    pairedUnion (forceOn (whiteBlock (G.incidentEdges (G.cluster (whiteProjection ω) x))) ∅ ω) \
        Percolation.internalEdges G.ends (G.cluster (whiteProjection ω) x)=
      pairedUnion ω \ Percolation.internalEdges G.ends (G.cluster (whiteProjection ω) x) := by
  rw [erased_pairedUnion,pairedUnion_eq]
  ext e
  constructor
  · rintro ⟨(⟨hew,_⟩ | heb),heI⟩
    · exact ⟨Or.inl hew,heI⟩
    · exact ⟨Or.inr heb,heI⟩
  · rintro ⟨(hew | heb),heI⟩
    · exact ⟨Or.inl ⟨hew,fun hQ => heI (G.white_edge_incident_cluster_internal _ x e hew hQ)⟩,heI⟩
    · exact ⟨Or.inr heb,heI⟩

end CriticalPercolation.BondGraph

end

end OAI
