import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.Measurability

namespace OAI

/-! Counting encounter vertices by mass transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutIso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (x : V) : cutVertex H x ≃g cutVertex K (f x) where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro a b
    change (K.Adj (f a) (f b) ∧ f a ≠ f x ∧ f b ≠ f x) ↔
      (H.Adj a b ∧ a ≠ x ∧ b ≠ x)
    simp only [f.map_adj_iff,f.injective.ne_iff]

theorem branchCount_iso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (S : Finset V) (x : V) :
    branchCount K (S.image f) (f x) = branchCount H S x := by
  unfold branchCount
  rw [←Finset.image_erase f.injective,Finset.image_image]
  let e := (cutIso f x).connectedComponentEquiv
  have he : ((S.erase x).image (fun a => (cutVertex K (f x)).connectedComponentMk (f a))) =
      (((S.erase x).image (cutVertex H x).connectedComponentMk).image e) := by
    rw [Finset.image_image]
    rfl
  change ((S.erase x).image (fun a => (cutVertex K (f x)).connectedComponentMk (f a))).card = _
  rw [he]
  exact Finset.card_image_iff.mpr e.injective.injOn

theorem clusterFinset_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (clusterFinset G (b ⁻¹' ω) x).image a = clusterFinset G ω (a x) := by
  have hi : (cluster G (b ⁻¹' ω) x).Infinite ↔ (cluster G ω (a x)).Infinite := by
    rw [←cluster_aut G hab]
    exact (Set.infinite_image_iff a.injective.injOn).symm
  by_cases hf : (cluster G (b ⁻¹' ω) x).Finite
  · have hf' : (cluster G ω (a x)).Finite := by
      rw [←cluster_aut G hab]
      exact hf.image a
    apply Finset.coe_injective
    simp only [Finset.coe_image,clusterFinset_coe G _ _ hf,clusterFinset_coe G _ _ hf']
    exact cluster_aut G hab ω x
  · have hf' : ¬(cluster G ω (a x)).Finite := hi.mp hf
    simp only [clusterFinset,dite_eq_right hf,dite_eq_right hf',Finset.image_empty]

theorem measurable_branchCount_pair [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) :
    Measurable (fun z : Set E × Finset V => branchCount (openSimpleGraph G z.1) z.2 x) :=
  measurable_from_prod_countable_left (fun S => measurable_branchCount G S x)

noncomputable def markedCluster (G : BondGraph V E) (ω η : Set E) (x : V) : Finset V :=
  (clusterFinset G η x).filter (IsEncounter G ω)

noncomputable def encounterCount (G : BondGraph V E) (ω η : Set E) (x : V) : ℕ :=
  if IsEncounter G ω x then branchCount (openSimpleGraph G ω) (markedCluster G ω η x) x else 0

theorem markedCluster_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω η : Set E) (x : V) :
    (markedCluster G (b ⁻¹' ω) (b ⁻¹' η) x).image a = markedCluster G ω η (a x) := by
  unfold markedCluster
  rw [←clusterFinset_aut G a b hab η x,Finset.filter_image]
  simp only [isEncounter_aut_iff G a b hab]

theorem encounterCount_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω η : Set E) (x : V) :
    encounterCount G (b ⁻¹' ω) (b ⁻¹' η) x = encounterCount G ω η (a x) := by
  simp only [encounterCount,isEncounter_aut_iff G a b hab]
  congr 1
  rw [←markedCluster_aut G a b hab]
  exact (branchCount_iso (openAutIso G a b hab ω) _ x).symm

theorem measurable_markedCluster [Countable V] [Countable E]
    (G : BondGraph V E) (p q : unitInterval) (x : V) :
    Measurable (fun l : E → unitInterval => markedCluster G (openEdges l p) (openEdges l q) x) :=
  measurable_filter_finset _ ((measurable_clusterFinset G x).comp (measurable_openEdges q)) _
    (fun y => (measurableSet_isEncounter G y).preimage (measurable_openEdges p))

theorem measurable_encounterCount [Countable V] [Countable E]
    (G : BondGraph V E) (p q : unitInterval) (x : V) :
    Measurable (fun l : E → unitInterval => encounterCount G (openEdges l p) (openEdges l q) x) := by
  apply Measurable.ite ((measurableSet_isEncounter G x).preimage (measurable_openEdges p)) _ measurable_const
  exact (measurable_branchCount_pair G x).comp
    ((measurable_openEdges p).prodMk (measurable_markedCluster G p q x))

theorem cluster_induce_connected (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω) (x : V) :
    ((openSimpleGraph G ω).induce (cluster G η x)).Connected := by
  let H := openSimpleGraph G η
  have he : cluster G η x = (H.connectedComponentMk x).supp := by
    ext y
    simp only [cluster,Set.mem_ofPred_eq,ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]
    exact (conn_iff_reachable G η x y).trans SimpleGraph.reachable_comm
  rw [he]
  apply SimpleGraph.Connected.mono (G := H.induce (H.connectedComponentMk x).supp)
  · intro a b hab
    exact ⟨hab.1,by obtain ⟨e,he,hGe⟩ := hab.2; exact ⟨e,hsub he,hGe⟩⟩
  · exact (H.connectedComponentMk x).connected_toSimpleGraph

theorem markedCluster_eq_of_conn (G : BondGraph V E) (ω η : Set E) {x y : V}
    (hxy : Conn G η x y) : markedCluster G ω η x = markedCluster G ω η y := by
  unfold markedCluster clusterFinset
  simp only [cluster_eq_of_conn G η hxy]

theorem sum_encounterCount_le (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω) (x : V)
    (hf : (cluster G η x).Finite) :
    (∑ y ∈ clusterFinset G η x, encounterCount G ω η y) ≤
      2*(markedCluster G ω η x).card := by
  let D := clusterFinset G η x
  let S := markedCluster G ω η x
  have hSD : S ⊆ D := Finset.filter_subset _ _
  have hDeq : (D:Set V) = cluster G η x := clusterFinset_coe G η x hf
  have hDconn : ((openSimpleGraph G ω).induce (D:Set V)).Connected :=
    hDeq ▸ cluster_induce_connected G ω η hsub x
  have he : (∑ y ∈ D, encounterCount G ω η y) =
      ∑ y ∈ S, branchCount (openSimpleGraph G ω) S y := by
    calc
      _ = ∑ y ∈ D, if IsEncounter G ω y then branchCount (openSimpleGraph G ω) S y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hxy : Conn G η x y := by
          change y ∈ cluster G η x
          rw [←hDeq]
          exact hy
        rw [encounterCount,←markedCluster_eq_of_conn G ω η hxy]
      _ = _ := (Finset.sum_filter _ _).symm
  rw [he]
  by_cases hs : S.Nonempty
  · exact (Nat.le_add_right _ 2).trans (sum_branchCount_le (openSimpleGraph G ω) S D hs hSD hDconn)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

end Percolation

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_average_eq_sum (G : BondGraph V E) (η : Set E) (x : V)
    (hf : (cluster G η x).Finite) (f : V → ℝ≥0∞) :
    (∑' y, clusterAveragingKernel G η x y * f y) =
      ((cluster G η x).ncard : ℝ≥0∞)⁻¹ * ∑ y ∈ clusterFinset G η x, f y := by
  rw [tsum_eq_sum (s := clusterFinset G η x)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hc : Conn G η x y := by
      change y ∈ cluster G η x
      rw [←clusterFinset_coe G η x hf]
      exact hy
    simp only [clusterAveragingKernel,ite_eq_left hc]
  · intro y hy
    have hc : ¬Conn G η x y := by
      intro h
      apply hy
      have hm : y ∈ cluster G η x := h
      rwa [←clusterFinset_coe G η x hf] at hm
    simp only [clusterAveragingKernel,ite_eq_right hc,zero_mul]

theorem average_encounterCount_le (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω)
    (x : V) (hf : (cluster G η x).Finite) :
    (∑' y, clusterAveragingKernel G η x y * (encounterCount G ω η y : ℝ≥0∞)) ≤
      2 * ∑' y, clusterAveragingKernel G η x y * (if IsEncounter G ω y then 1 else 0) := by
  rw [cluster_average_eq_sum G η x hf,cluster_average_eq_sum G η x hf]
  have hc : (∑ y ∈ clusterFinset G η x, (encounterCount G ω η y : ℝ≥0∞)) ≤
      2 * (markedCluster G ω η x).card := by
    exact_mod_cast sum_encounterCount_le G ω η hsub x hf
  have he : (∑ y ∈ clusterFinset G η x, (if IsEncounter G ω y then (1:ℝ≥0∞) else 0)) =
      (markedCluster G ω η x).card := by
    rw [←Finset.sum_filter]
    simp only [markedCluster,Finset.sum_const,nsmul_one]
  rw [he,←mul_assoc, mul_comm (2:ℝ≥0∞),mul_assoc]
  exact mul_le_mul_right hc _

theorem expected_encounterCount_le [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (p q : unitInterval) (hqp : q ≤ p)
    (hfin : ∀ x, ∀ᵐ ω ∂law q, (cluster G ω x).Finite) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (encounterCount G (openEdges l p) (openEdges l q) (root i) : ℝ≥0∞) ∂labelLaw) ≤
    2 * (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l p) (root i) then 1 else 0) ∂labelLaw) := by
  have ha := label_root_cluster_average G hconn hloc root weight htr hw q hfin
    (fun l x => (encounterCount G (openEdges l p) (openEdges l q) x : ℝ≥0∞))
    (fun x => (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_encounterCount G p q x))
    (fun a b hab l x => by exact_mod_cast encounterCount_aut G a b hab (openEdges l p) (openEdges l q) x)
  have hb := label_root_cluster_average G hconn hloc root weight htr hw q hfin
    (fun l x => if IsEncounter G (openEdges l p) x then (1:ℝ≥0∞) else 0)
    (fun x => Measurable.ite ((measurableSet_isEncounter G x).preimage (measurable_openEdges p))
      measurable_const measurable_const)
    (fun a b hab l x => by simp only [show openEdges (l ∘ b) p = b ⁻¹' openEdges l p from rfl,
      isEncounter_aut_iff G a b hab])
  rw [←ha,←hb,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_assoc,mul_comm (2:ℝ≥0∞),mul_assoc]
  apply mul_le_mul_right
  rw [←lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  apply lintegral_mono_ae
  have hfl : ∀ᵐ l ∂labelLaw, (cluster G (openEdges l q) (root i)).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω (root i)).Finite) (measurable_openEdges q).aemeasurable
    rw [map_openEdges]
    exact hfin (root i)
  filter_upwards [hfl] with l hl
  exact average_encounterCount_le G _ _ (openEdges_mono l hqp) (root i) hl
end Percolation

end OAI
