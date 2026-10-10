import OAI.Probability.BenjaminiSchramm.IntrinsicBallExposure
import OAI.Probability.BenjaminiSchramm.FreshSlabCrossing
import OAI.Probability.BenjaminiSchramm.ClusterExposure
import OAI.Probability.BenjaminiSchramm.PhaseInput
import OAI.Probability.BenjaminiSchramm.LayerMomentDecomposition

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def openFrontier (ω : Set E) (S : Set V) : Set V :=
  {z | z ∉ S ∧ ∃ u ∈ S, ∃ e ∈ ω, G e = s(u,z)}

lemma openFrontier_dependsOn (S : Set V) :
    DependsOn (fun ω => openFrontier G ω S) (ballIncidentEdges G S) := by
  intro ω η hωη
  ext z
  constructor
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mp he,heq⟩
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mpr he,heq⟩

lemma openFrontier_finite (hloc : LocallyFinite G) (ω : Set E)
    {S : Set V} (hS : S.Finite) : (openFrontier G ω S).Finite := by
  apply (hS.biUnion (fun u _ => finite_neighbors hloc u)).subset
  rintro z ⟨_,u,hu,e,_,heq⟩
  exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,e,heq⟩⟩

lemma measurable_mem_openFrontier [Countable V] [Countable E] (S : Set V) (z : V) :
    Measurable (fun ω => z ∈ openFrontier G ω S) := by
  exact measurable_const.and (Measurable.exists fun u => measurable_const.and
    (Measurable.exists fun e => (measurable_set_mem e).and measurable_const))

lemma measurableSet_openFrontier_eq [Countable V] [Countable E] (S F : Set V) :
    MeasurableSet {ω | openFrontier G ω S = F} := by
  have he : {ω | openFrontier G ω S = F} =
      ⋂ z : V, {ω | (z ∈ openFrontier G ω S) ↔ z ∈ F} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact Set.ext_iff
  rw [he]
  exact MeasurableSet.iInter fun z =>
    ((measurable_mem_openFrontier G S z).iff measurable_const).setOf

lemma restricted_exactCluster_dependsOn (I : Set E) (x : V) (S : Set V) :
    DependsOn (fun ω => cluster G (ω ∩ I) x = S) (ballIncidentEdges G S) := by
  intro ω η hωη
  have ha : ∀ e ∈ (criticalModel G).incidentEdges S,
      (e ∈ Set.inter ω I) = (e ∈ Set.inter η I) := by
    intro e he
    exact congrArg (fun p : Prop => p ∧ e ∈ I) (hωη e he)
  have hh := (criticalModel G).exactCluster_dependsOn x S ha
  change ((criticalModel G).cluster (Set.inter ω I) x = S) =
    ((criticalModel G).cluster (Set.inter η I) x = S) at hh
  rw [criticalModel_cluster,criticalModel_cluster] at hh
  exact hh

lemma measurableSet_restricted_exactCluster [Countable V] [Countable E]
    (I : Set E) (x : V) (S : Set V) :
    MeasurableSet {ω | cluster G (ω ∩ I) x = S} := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  simpa only [criticalModel_cluster,Set.preimage_ofPred_eq] using
    ((criticalModel G).measurableSet_exactCluster x S).preimage hm

def lowerFrontierCell (I J : Set E) (x : V) (S F : Set V) : Set (Set E) :=
  {ω | cluster G (ω ∩ I) x = S ∧ openFrontier G (ω ∩ J) S = F}

lemma lowerFrontierCell_dependsOn (I J : Set E) (x : V) (S F : Set V) :
    DependsOn (fun ω => ω ∈ lowerFrontierCell G I J x S F) (ballIncidentEdges G S) := by
  intro ω η hωη
  have hc := restricted_exactCluster_dependsOn G I x S hωη
  change (cluster G (Set.inter ω I) x = S) =
    (cluster G (Set.inter η I) x = S) at hc
  have ha : ∀ e ∈ ballIncidentEdges G S,
      (e ∈ Set.inter ω J) = (e ∈ Set.inter η J) := by
    intro e he
    exact congrArg (fun p : Prop => p ∧ e ∈ J) (hωη e he)
  have hf := openFrontier_dependsOn G S ha
  change openFrontier G (Set.inter ω J) S = openFrontier G (Set.inter η J) S at hf
  change (cluster G (Set.inter ω I) x = S ∧ openFrontier G (Set.inter ω J) S = F) =
    (cluster G (Set.inter η I) x = S ∧ openFrontier G (Set.inter η J) S = F)
  rw [hc,hf]

lemma measurableSet_lowerFrontierCell [Countable V] [Countable E]
    (I J : Set E) (x : V) (S F : Set V) :
    MeasurableSet (lowerFrontierCell G I J x S F) := by
  have hm : Measurable (fun ω : Set E => ω ∩ J) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (measurableSet_restricted_exactCluster G I x S).inter
    ((measurableSet_openFrontier_eq G S F).preimage hm)

theorem conn_last_exit_frontier (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) (hc : Conn G ω x y) :
    ∃ z ∈ openFrontier G ω S, Conn G (ω \ ballIncidentEdges G S) z y := by
  revert hy
  induction hc with
  | refl => exact fun hy => (hy hx).elim
  | @tail a b hxa hab ih =>
    intro hy
    obtain ⟨e,he,heq⟩ := hab
    by_cases ha : a ∈ S
    · exact ⟨b,⟨hy,a,ha,e,he,heq⟩,conn_refl G _ b⟩
    · obtain ⟨z,hz,hza⟩ := ih ha
      refine ⟨z,hz,hza.tail ⟨e,⟨he,?_⟩,heq⟩⟩
      rintro ⟨u,hu,hue⟩
      rw [heq,Sym2.mem_iff] at hue
      rcases hue with rfl | rfl
      · exact ha hu
      · exact hy hu

lemma openFrontier_lowerCluster_outside (ω : Set E) (D : Set V) (x : V)
    (hx : x ∈ D) {z : V}
    (hz : z ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G D) x)) : z ∉ D := by
  rintro hzD
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have huD := conn_internalEdges_end_mem G ω D hx hu
  apply hz
  exact hu.tail ⟨e,⟨he,(mem_internalEdges_of_ends G D e u z heq).mpr ⟨huD,hzD⟩⟩,heq⟩

theorem lowerCluster_new_vertex_cover (ω : Set E) (D U : Set V) (x y : V)
    (hy : y ∉ cluster G (ω ∩ internalEdges G D) x)
    (hc : Conn G (ω ∩ internalEdges G U) x y) :
    ∃ z ∈ openFrontier G (ω ∩ internalEdges G U)
        (cluster G (ω ∩ internalEdges G D) x),
      Conn G ((ω ∩ internalEdges G U) \
        ballIncidentEdges G (cluster G (ω ∩ internalEdges G D) x)) z y :=
  conn_last_exit_frontier G _ _ (mem_cluster_self G _ x) hy hc

def restrictedLayerCount (I : Set E) (A : Set V) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if y ∈ A ∧ Conn G (ω ∩ I) x y then 1 else 0

lemma measurable_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (x : V) : Measurable (fun ω => restrictedLayerCount G I A ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and ((measurableSet_conn G x y).mem.comp hm)).setOf
    measurable_const measurable_const

lemma restrictedLayerCount_dependsOn (I : Set E) (A : Set V) (x : V) :
    DependsOn (fun ω => restrictedLayerCount G I A ω x) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (∑' y, if y ∈ A ∧ Conn G (Set.inter ω I) x y then (1 : ℝ≥0∞) else 0) =
    (∑' y, if y ∈ A ∧ Conn G (Set.inter η I) x y then (1 : ℝ≥0∞) else 0)
  rw [he]

lemma restrictedLayerCount_mono_edges {I J : Set E} (hIJ : I ⊆ J)
    (A : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x ≤ restrictedLayerCount G J A ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ I) x y
  · rw [ite_eq_left hy,ite_eq_left
      ⟨hy.1,conn_mono G (Set.inter_subset_inter_right _ hIJ) hy.2⟩]
  · rw [ite_eq_right hy]
    exact bot_le

theorem layerCount_le_frontier_sum (ω : Set E) (I J : Set E)
    (x : V) (S : Set V) (F : Finset V) (A : Set V)
    (hcell : ω ∈ lowerFrontierCell G I J x S (F : Set V)) :
    restrictedLayerCount G J (A \ S) ω x ≤
      ∑ z ∈ F, restrictedLayerCount G (J \ ballIncidentEdges G S) A ω z := by
  rw [show (∑ z ∈ F, restrictedLayerCount G (J \ ballIncidentEdges G S) A ω z) =
      ∑' y, ∑ z ∈ F, if y ∈ A ∧
        Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y then (1 : ℝ≥0∞) else 0 by
    exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A \ S ∧ Conn G (ω ∩ J) x y
  · rw [ite_eq_left hy]
    obtain ⟨z,hz,hzy⟩ := conn_last_exit_frontier G (ω ∩ J) S
      (hcell.1 ▸ mem_cluster_self G (ω ∩ I) x) hy.1.2 hy.2
    have hzF : z ∈ F := by
      change z ∈ (F : Set V)
      rwa [←hcell.2]
    have he : Set.inter ω (Set.diff J (ballIncidentEdges G S)) =
        Set.diff (Set.inter ω J) (ballIncidentEdges G S) := by
      ext e
      exact and_assoc.symm
    have hzterm : (if y ∈ A ∧ Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y
        then (1 : ℝ≥0∞) else 0) = 1 := by
      have hc' : Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y := by
        change Conn G (Set.inter ω (Set.diff J (ballIncidentEdges G S))) z y
        rw [he]
        exact hzy
      rw [ite_eq_left ⟨hy.1.1,hc'⟩]
    exact hzterm.symm.le.trans (Finset.single_le_sum
      (f := fun z => if y ∈ A ∧ Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y
        then (1 : ℝ≥0∞) else 0) (fun _ _ => bot_le) hzF)
  · rw [ite_eq_right hy]
    exact bot_le

theorem lowerFrontierCell_fractional_bound [Countable V] [Countable E]
    (q : E → unitInterval) (I J : Set E) (x : V) (S : Set V)
    (F : Finset V) (A : Set V) {a b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F,
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, (lowerFrontierCell G I J x S (F : Set V)).indicator
      (fun ω => restrictedLayerCount G J (A \ S) ω x^(a*b)) ω
        ∂CriticalPercolation.BernoulliProduct.law q) ≤
      CriticalPercolation.BernoulliProduct.law q
        (lowerFrontierCell G I J x S (F : Set V)) * (F.card : ℝ≥0∞)^b*L^b := by
  let Q := ballIncidentEdges G S
  let f : V → Set E → ℝ≥0∞ := fun z ω => restrictedLayerCount G (J \ Q) A ω z
  let g : Set E → ℝ≥0∞ := fun ω => ∑ z ∈ F, f z ω
  have hf (z : V) : Measurable (f z) := measurable_restrictedLayerCount G _ A z
  have hg : Measurable g := Finset.measurable_sum F (fun z _ => hf z)
  have hd : DependsOn g Qᶜ := by
    intro ω η hωη
    apply Finset.sum_congr rfl
    intro z _
    exact restrictedLayerCount_dependsOn G (J \ Q) A z (fun e he => hωη e he.2)
  have hLf (z : V) (hz : z ∈ F) :
      (∫⁻ ω, f z ω^a ∂CriticalPercolation.BernoulliProduct.law q) ≤ L := by
    exact le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (restrictedLayerCount_mono_edges G (I := J \ Q) (J := J)
        Set.sdiff_subset A ω z) ha.le) (hL z hz)
  have hbound := exposed_frontier_fractional_bound q Q
    (lowerFrontierCell G I J x S (F : Set V))
    (measurableSet_lowerFrontierCell G I J x S _) (lowerFrontierCell_dependsOn G I J x S _)
    F f (fun z _ => hf z) g hg hd (fun _ => le_rfl) ha ha1 hb hb1 L hLf
  apply le_trans (lintegral_mono ?_) hbound
  intro ω
  by_cases hω : ω ∈ lowerFrontierCell G I J x S (F : Set V)
  · simp only [Set.indicator_of_mem hω]
    exact ENNReal.rpow_le_rpow (layerCount_le_frontier_sum G ω I J x S F A hω)
      (mul_nonneg ha.le hb.le)
  · simp only [Set.indicator_of_notMem hω,le_refl]

end Percolation.BenjaminiSchramm

end

end OAI
