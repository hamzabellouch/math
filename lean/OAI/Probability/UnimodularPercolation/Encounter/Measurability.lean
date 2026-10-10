import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.Vertices

namespace OAI

/-! Measurability of branches and finite clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_image_eq_minima [Encodable V] {W : Type*} (S : Finset V) (f : V → W) :
    (S.image f).card =
      (S.filter (fun y => ∀ z ∈ S, f z = f y → Encodable.encode y ≤ Encodable.encode z)).card := by
  let R := S.filter (fun y => ∀ z ∈ S, f z = f y → Encodable.encode y ≤ Encodable.encode z)
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hinj : Set.InjOn f (R:Set V) := by
    intro y hy z hz he
    apply Encodable.encode_injective
    exact le_antisymm ((Finset.mem_filter.mp hy).2 z (hRS hz) he.symm)
      ((Finset.mem_filter.mp hz).2 y (hRS hy) he)
  have he : R.image f = S.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image hRS)
    intro c hc
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨z,hz,hmin⟩ := (S.filter (fun z => f z = f y)).exists_min_image
      Encodable.encode ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩⟩
    refine Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,?_⟩,
      (Finset.mem_filter.mp hz).2⟩
    intro w hw hwe
    exact hmin w (Finset.mem_filter.mpr ⟨hw,hwe.trans (Finset.mem_filter.mp hz).2⟩)
  rw [←he]
  exact Finset.card_image_iff.mpr hinj

theorem measurable_branchCount [Countable V] [Countable E]
    (G : BondGraph V E) (S : Finset V) (x : V) :
    Measurable (fun ω => branchCount (openSimpleGraph G ω) S x) := by
  let : Encodable V := Encodable.ofCountable V
  have he (ω : Set E) : branchCount (openSimpleGraph G ω) S x =
      ∑ y ∈ S.erase x, if (∀ z ∈ S.erase x, Conn G (cutConfig G ω x) z y →
        Encodable.encode y ≤ Encodable.encode z) then 1 else 0 := by
    rw [branchCount,card_image_eq_minima,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    simp only [ConnectedComponent.eq,cutVertex_open,←conn_iff_reachable]
  simp_rw [he]
  apply Finset.measurable_sum
  intro y hy
  apply Measurable.ite _ measurable_const measurable_const
  have he' : {ω : Set E | ∀ z ∈ S.erase x, Conn G (cutConfig G ω x) z y →
      Encodable.encode y ≤ Encodable.encode z} =
      ⋂ z ∈ S.erase x, ({ω | Conn G (cutConfig G ω x) z y}ᶜ ∪
        {ω : Set E | Encodable.encode y ≤ Encodable.encode z}) := by ext ω; simp [imp_iff_not_or]
  rw [he']
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro _
  exact ((measurableSet_conn G z y).preimage (measurable_cutConfig G x)).compl.union
    (by by_cases hh : Encodable.encode y ≤ Encodable.encode z <;> simp [hh])

noncomputable def clusterFinset (G : BondGraph V E) (ω : Set E) (x : V) : Finset V :=
  if h : (cluster G ω x).Finite then h.toFinset else ∅

theorem clusterFinset_coe (G : BondGraph V E) (ω : Set E) (x : V)
    (h : (cluster G ω x).Finite) : (clusterFinset G ω x : Set V) = cluster G ω x := by
  simp [clusterFinset,h]

theorem measurable_clusterFinset [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : Measurable (fun ω => clusterFinset G ω x) := by
  apply measurable_to_countable
  intro ω₀
  let S := clusterFinset G ω₀ x
  have he : {ω | clusterFinset G ω x = S} =
      {ω | cluster G ω x = (S:Set V)} ∪
        ({ω | (cluster G ω x).Infinite} ∩ {ω : Set E | S = ∅}) := by
    ext ω
    by_cases h : (cluster G ω x).Finite
    · simp only [Set.mem_ofPred,Set.mem_union,Set.mem_inter_iff,clusterFinset,dite_eq_left h]
      simp only [Set.Infinite,h,not_true_eq_false,false_and,or_false]
      constructor
      · intro he; rw [←he,h.coe_toFinset]
      · intro he; exact Finset.coe_injective (h.coe_toFinset.trans he)
    · simp only [Set.mem_ofPred,Set.mem_union,Set.mem_inter_iff,clusterFinset,dite_eq_right h]
      have hn : cluster G ω x ≠ (S:Set V) := fun he => h (he ▸ S.finite_toSet)
      simp [hn,Set.Infinite,h,eq_comm]
  change MeasurableSet {ω | clusterFinset G ω x = S}
  rw [he]
  exact (measurableSet_cluster_eq G x (S:Set V)).union
    ((measurableSet_infinite_cluster G x).inter (by by_cases hs : S = ∅ <;> simp [hs]))

theorem measurable_filter_finset {Ω : Type*} [MeasurableSpace Ω] [Countable V]
    (S : Ω → Finset V) (hS : Measurable S) (P : Ω → V → Prop)
    (hP : ∀ x, MeasurableSet {ω | P ω x}) :
    Measurable (fun ω => (S ω).filter (P ω)) := by
  have hf (D : Finset V) : Measurable (fun ω => D.filter (P ω)) := by
    apply measurable_to_countable
    intro ω₀
    have he : {ω | D.filter (P ω) = D.filter (P ω₀)} =
        ⋂ y, {ω | (y ∈ D ∧ P ω y) ↔ y ∈ D.filter (P ω₀)} := by
      ext ω; simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.ext_iff,Finset.mem_filter]
    change MeasurableSet {ω | D.filter (P ω) = D.filter (P ω₀)}
    rw [he]
    apply MeasurableSet.iInter
    intro y
    by_cases hy : y ∈ D
    · by_cases hp : P ω₀ y <;> simp only [hy,hp,Finset.mem_filter,true_and,iff_true,iff_false]
      · exact hP y
      · exact (hP y).compl
    · simp [hy]
  have hm : Measurable (fun z : Ω × Finset V => z.2.filter (P z.1)) :=
    measurable_from_prod_countable_left hf
  exact hm.comp (measurable_id.prodMk hS)

end Percolation

end OAI
