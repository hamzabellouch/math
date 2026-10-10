import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Criticality.NestedLayerBlock

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma measurableSet_block_of_dependsOn (A : Set (Set E)) (L : Set E)
    (hA : MeasurableSet A) (hdep : DependsOn (fun ω : Set E => ω∈A) L) :
    MeasurableSet[blockSigma L] A := by
  have he : A=(fun ω : Set E => ω∩L) ⁻¹' A := by
    ext ω
    exact (hdep (x := ω) (y := (show Set E from ω∩L))
      (fun e he => propext (show e∈ω ↔ e∈ω∩L from by simp [he]))).to_iff
  rw [he]
  exact hA.preimage (measurable_inter_block L)
end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def entrySeeds (D : Set V) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩(G.inducedEdges D)ᶜ) o ∩ D

lemma entrySeeds_subset_cluster (D : Set V) (o : V) (ω : Set E) :
    G.entrySeeds D o ω⊆G.cluster ω o :=
  fun _ h => G.cluster_mono Set.inter_subset_left o h.1

lemma measurable_entrySeeds [Countable V] [Countable E] (D : Set V) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges D)ᶜ) inferInstance
      (G.entrySeeds D o) := by
  let : MeasurableSpace (Set E) := blockSigma (G.inducedEdges D)ᶜ
  change Measurable (G.entrySeeds D o)
  apply Measurable.of_eval
  intro x
  exact (((measurable_pi_apply x).comp ((G.measurable_cluster o).comp
    (measurable_inter_block (G.inducedEdges D)ᶜ))).and measurable_const)

lemma measurableSet_entrySeed [Countable V] [Countable E] (D : Set V) (o x : V) :
    MeasurableSet[blockSigma (G.inducedEdges D)ᶜ] {ω | x∈G.entrySeeds D o ω} := by
  let : MeasurableSpace (Set E) := blockSigma (G.inducedEdges D)ᶜ
  exact ((measurable_pi_apply x).comp (G.measurable_entrySeeds D o)).setOf

lemma entrySeed_eq_or_adj_exterior {D : Set V} {o x : V} {ω : Set E}
    (hx : x∈G.entrySeeds D o ω) :
    x=o ∨ ∃ y, y∉D ∧ G.fullGraph.Adj x y := by
  by_cases he : x=o
  · exact Or.inl he
  right
  obtain ⟨w⟩ := hx.1.symm
  obtain ⟨y,hxy,w',hw⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne he w
  obtain ⟨⟨e,heω,hexy⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  refine ⟨y,?_,G.openGraph_mono (Set.subset_univ _) hxy⟩
  intro hy
  apply heω.2
  intro z hz
  rw [hexy] at hz
  exact (Sym2.mem_iff.mp hz).elim (fun h => h ▸ hx.2) (fun h => h ▸ hy)

lemma entrySeeds_weight_band (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ a : ℝ, 0<a ∧ a≤1 ∧ ∀ o T, a*T≤1 → ∀ ω x,
      x∈G.entrySeeds (G.safeBallDomain o T R) o ω →
      a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  obtain ⟨B,hB,hball⟩ := G.modularRatio_ball_weight hc hl hq 1
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨1/(C*B),by positivity,?_,fun o T hroot ω x hx => ⟨?_,G.safeBallDomain_subset o T R hx.2⟩⟩
  · exact (div_le_one (by positivity)).mpr (by nlinarith : (1:ℝ)≤C*B)
  rcases G.entrySeed_eq_or_adj_exterior hx with rfl|⟨y,hy,hxy⟩
  · simpa only [G.modularRatio_self] using hroot
  have hlower : T/C<G.modularRatio y o := lt_of_not_ge (fun hh => hy (hlow o T hh))
  have hbound : G.modularRatio y o≤B*G.modularRatio x o :=
    hball o y x (G.vertexBall_comm.mp (G.vertexBall_step (G.mem_vertexBall_self x 0) hxy))
  have : T<(G.modularRatio x o)*(C*B) := by
    have hh := (div_lt_iff₀ hC0).mp (hlower.trans_le hbound)
    nlinarith
  have hh := (div_lt_iff₀ (mul_pos hC0 hB0)).mpr this
  simpa only [one_div,inv_mul_eq_div] using hh.le

lemma entrySeeds_weight_band_start (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ a U : ℝ, 0<a ∧ 0<U ∧ a*U≤1 ∧ (∀ o, o∈G.safeBallDomain o U R) ∧
      ∀ o T, a*T≤1 → ∀ ω x,
      x∈G.entrySeeds (G.safeBallDomain o T R) o ω →
      a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  obtain ⟨B,hB,hball⟩ := G.modularRatio_ball_weight hc hl hq 1
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨1/(C*B),C,by positivity,hC0,?_,?_,fun o T hroot ω x hx => ⟨?_,G.safeBallDomain_subset o T R hx.2⟩⟩
  · have he : (1/(C*B))*C=1/B := by field_simp
    rw [he]
    exact (div_le_one hB0).mpr hB
  · intro o
    apply hlow o C
    change G.modularRatio o o≤C/C
    rw [G.modularRatio_self,div_self hC0.ne']
  rcases G.entrySeed_eq_or_adj_exterior hx with rfl|⟨y,hy,hxy⟩
  · simpa only [G.modularRatio_self] using hroot
  have hlower : T/C<G.modularRatio y o := lt_of_not_ge (fun hh => hy (hlow o T hh))
  have hbound : G.modularRatio y o≤B*G.modularRatio x o :=
    hball o y x (G.vertexBall_comm.mp (G.vertexBall_step (G.mem_vertexBall_self x 0) hxy))
  have : T<(G.modularRatio x o)*(C*B) := by
    have hh := (div_lt_iff₀ hC0).mp (hlower.trans_le hbound)
    nlinarith
  have hh := (div_lt_iff₀ (mul_pos hC0 hB0)).mpr this
  simpa only [one_div,inv_mul_eq_div] using hh.le

lemma layerStopped_eq (D H : Set V) (ω : Set E) :
    ((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩G.inducedEdges Hᶜ =
      (ω∩G.inducedEdges D)∩G.inducedEdges Hᶜ := by
  ext e
  constructor
  · exact fun h => ⟨⟨h.1.1.1,h.1.2⟩,h.2⟩
  · intro h
    refine ⟨⟨⟨h.1.1,h.1.2,?_⟩,h.1.2⟩,h.2⟩
    intro he
    obtain ⟨x,y,hxy⟩ : ∃ x y, G.ends e=s(x,y) := Sym2.exists.mp ⟨G.ends e,rfl⟩
    have hx : x∈G.ends e := by rw [hxy]; simp
    exact h.2 x hx (he x hx)

lemma domainLayer_restrict (D H : Set V) (x : V) (hx : x∉H) (N : ℕ)
    (ω : Set E) :
    ω∩(G.inducedEdges D\G.inducedEdges H)∈G.domainFreshExitEvent D Hᶜ x N ↔
      ω∈G.domainFreshExitEvent D Hᶜ x N := by
  constructor
  · exact G.domainFreshExitEvent_upper hx N Set.inter_subset_left
  · rintro ⟨F,hF,hFe⟩
    refine ⟨F,hF,?_⟩
    intro e he
    obtain ⟨⟨⟨u,v,hev,hu,hv⟩,heH⟩,heω,heD⟩ := hFe he
    have hvH := G.cluster_induced_subset (ω∩G.inducedEdges D) Hᶜ hx hv
    have hn : e∉G.inducedEdges H := by
      intro hh
      exact hvH (hh v (by rw [hev]; simp))
    have hu' : u∉G.cluster (((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩
        G.inducedEdges Hᶜ) x := by
      rw [G.layerStopped_eq]
      exact hu
    have hv' : v∈G.cluster (((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩
        G.inducedEdges Hᶜ) x := by
      rw [G.layerStopped_eq]
      exact hv
    exact ⟨⟨⟨u,v,hev,hu',hv'⟩,heH⟩,⟨heω,heD,hn⟩,heD⟩

lemma boundedLayer_restrict (D H : Set V) (x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞)
    (ω : Set E) :
    ω∩(G.inducedEdges D\G.inducedEdges H)∈G.boundedDomainFreshExitEvent D Hᶜ x N M ↔
      ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M := by
  simp only [boundedDomainFreshExitEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.layerStopped_eq,G.domainLayer_restrict D H x hx N ω]

lemma measurableSet_boundedDomainFreshExit [Countable V] [Countable E]
    (D S : Set V) (x : V) (hx : x∈S) (N : ℕ) (M : ℝ≥0∞) :
    MeasurableSet (G.boundedDomainFreshExitEvent D S x N M) := by
  apply (G.measurableSet_domainFreshExitEvent hx N).inter
  apply measurableSet_le _ measurable_const
  exact (G.measurable_modularClusterMass x x).comp
    (((measurable_inter_block (G.inducedEdges S)).mono (blockSigma_le _) le_rfl).comp
      ((measurable_inter_block (G.inducedEdges D)).mono (blockSigma_le _) le_rfl))

lemma measurableSet_boundedLayer [Countable V] [Countable E]
    (D H : Set V) (x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞) :
    MeasurableSet[blockSigma (G.inducedEdges D\G.inducedEdges H)]
      (G.boundedDomainFreshExitEvent D Hᶜ x N M) := by
  have he : G.boundedDomainFreshExitEvent D Hᶜ x N M=
      (fun ω : Set E => ω∩(G.inducedEdges D\G.inducedEdges H)) ⁻¹'
        G.boundedDomainFreshExitEvent D Hᶜ x N M := by
    ext ω
    exact (G.boundedLayer_restrict D H x hx N M ω).symm
  rw [he]
  exact (G.measurableSet_boundedDomainFreshExit D Hᶜ x hx N M).preimage (measurable_inter_block _)

lemma entry_good_independent [Countable V] [Countable E]
    (q : unitInterval) (D H : Set V) (o x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞) :
    (G.law q) ({ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M)=
      (G.law q) {ω | x∈G.entrySeeds D o ω}*
        (G.law q) (G.boundedDomainFreshExitEvent D Hᶜ x N M) := by
  have hdis : Disjoint (G.inducedEdges D)ᶜ (G.inducedEdges D\G.inducedEdges H) :=
    Set.disjoint_left.mpr (fun e he hf => he hf.1)
  simpa only [law,←law_const] using ((independent_disjoint_blocks (fun _ : E => q) _ _ hdis).indepSet_of_measurableSet
    (G.measurableSet_entrySeed D o x) (G.measurableSet_boundedLayer D H x hx N M)).measure_inter_eq_mul

end CriticalPercolation.BondGraph
end
end

end OAI
