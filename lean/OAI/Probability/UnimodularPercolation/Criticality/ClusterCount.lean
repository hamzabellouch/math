import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Criticality.Connectivity
import OAI.Probability.UnimodularPercolation.Criticality.Ergodicity
import OAI.Probability.UnimodularPercolation.Criticality.FiniteChanges

namespace OAI

/-! Exclusion of positive finite critical cluster counts. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem law_invariant_zero_one [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b →
      (fun ω : Set E => b ⁻¹' ω) ⁻¹' A = A) : law p A = 0 ∨ law p A = 1 := by
  have hm : law p A = labelLaw ((fun l => openEdges l p) ⁻¹' A) := by
    rw [←map_openEdges p,Measure.map_apply (measurable_openEdges p) hA]
  rw [hm]
  apply label_invariant_zero_one G hconn hloc hqt _ (hA.preimage (measurable_openEdges p))
  intro a b hab
  ext l
  have h := Set.ext_iff.mp (hinv a b hab) (openEdges l p)
  exact h

theorem unique_infinite_cluster_aut_iff (G : BondGraph V E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (ω : Set E) :
    (∃! C, C ∈ infiniteClusters G (b ⁻¹' ω)) ↔ ∃! C, C ∈ infiniteClusters G ω := by
  have hInf (x : V) : (cluster G (b ⁻¹' ω) x).Infinite ↔ (cluster G ω (a x)).Infinite := by
    rw [←cluster_aut G hab ω x]
    exact (Set.infinite_image_iff a.injective.injOn).symm
  rw [unique_infinite_cluster_iff,unique_infinite_cluster_iff]
  constructor
  · rintro ⟨x,hx,h⟩
    refine ⟨a x,(hInf x).mp hx,?_⟩
    intro y hy
    have hh : (cluster G (b ⁻¹' ω) (a.symm y)).Infinite := (hInf _).mpr (by simpa using hy)
    simpa only [Equiv.apply_symm_apply] using (conn_aut_iff G hab ω x (a.symm y)).mp (h _ hh)
  · rintro ⟨x,hx,h⟩
    refine ⟨a.symm x,(hInf _).mpr (by simpa using hx),?_⟩
    intro y hy
    apply (conn_aut_iff G hab ω (a.symm x) y).mpr
    simpa only [Equiv.apply_symm_apply] using h (a y) ((hInf y).mp hy)

theorem critical_unique_probability_zero [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) : law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} = 0 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  refine (law_invariant_zero_one G hconn hloc hqt (pc G) _
    (measurableSet_unique_infinite_cluster G) ?_).resolve_right
    (critical_not_ae_unique G hconn hloc hqt hh)
  intro a b hab
  ext ω
  exact unique_infinite_cluster_aut_iff G hab ω

def InfiniteCover (G : BondGraph V E) (R : Finset V) (ω : Set E) : Prop :=
  ∀ y, (cluster G ω y).Infinite → ∃ z ∈ R, Conn G ω y z

theorem measurableSet_infiniteCover [Countable V] [Countable E]
    (G : BondGraph V E) (R : Finset V) : MeasurableSet {ω | InfiniteCover G R ω} := by
  have he : {ω | InfiniteCover G R ω} =
      ⋂ y, ({ω | (cluster G ω y).Infinite}ᶜ ∪ ⋃ z ∈ R, {ω | Conn G ω y z}) := by
    ext ω
    simp only [InfiniteCover,Set.mem_iInter,Set.mem_union,Set.mem_compl_iff,
      Set.mem_iUnion,Set.mem_ofPred_eq,imp_iff_not_or]
    simp only [exists_prop]
  rw [he]
  exact MeasurableSet.iInter fun y => (measurableSet_infinite_cluster G y).compl.union
    (R.measurableSet_biUnion fun z _ => measurableSet_conn G y z)

theorem unique_pos_of_cover_pos [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (p : unitInterval) (hp : 0 < p)
    (hp1 : p < 1) (x : V) (R : Finset V)
    (hpos : 0 < law p {ω | (cluster G ω x).Infinite ∧ InfiniteCover G R ω}) :
    0 < law p {ω | ∃! C, C ∈ infiniteClusters G ω} := by
  obtain ⟨F,hF⟩ := finite_connecting_edges G hconn x R
  apply finiteOverwrite_pos p hp hp1 F F (Finset.Subset.refl _)
    {ω | (cluster G ω x).Infinite ∧ InfiniteCover G R ω} _
    (measurableSet_unique_infinite_cluster G) hpos
  rintro ω ⟨hx,hcover⟩
  have how : finiteOverwrite F F ω = ω ∪ (F:Set E) := by
    ext e
    simp only [finiteOverwrite,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  rw [how]
  apply finite_opening_unique G ω F x hx
  intro y hy
  obtain ⟨z,hz,hyz⟩ := hcover y hy
  exact conn_trans G _ (conn_mono G Set.subset_union_right (hF z hz))
    (conn_mono G Set.subset_union_left (conn_symm G _ hyz))

theorem critical_infiniteCover_survival_zero [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (x : V) (R : Finset V) :
    law (pc G) {ω | (cluster G ω x).Infinite ∧ InfiniteCover G R ω} = 0 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  by_contra h
  have hp := unique_pos_of_cover_pos G hconn (pc G) (pc_pos G hloc hqt)
    (pc_lt_one_of_nonamenable G hconn hloc hqt hh) x R (pos_iff_ne_zero.mpr h)
  rw [critical_unique_probability_zero G hconn hloc hqt hh] at hp
  exact lt_irrefl _ hp

theorem critical_finite_count_empty_ae [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) :
    ∀ᵐ ω ∂law (pc G), (infiniteClusters G ω).Finite → infiniteClusters G ω = ∅ := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have ha (x : V) (R : Finset V) :
      ∀ᵐ ω ∂law (pc G), ¬((cluster G ω x).Infinite ∧ InfiniteCover G R ω) := by
    apply ae_iff.mpr
    simpa only [not_not] using critical_infiniteCover_survival_zero G hconn hloc hqt hh x R
  have hall : ∀ᵐ ω ∂law (pc G), ∀ x : V, ∀ R : Finset V,
      ¬((cluster G ω x).Infinite ∧ InfiniteCover G R ω) := by
    exact ae_all_iff.mpr fun x => ae_all_iff.mpr (ha x)
  filter_upwards [hall] with ω hω
  intro hfin
  by_contra hn
  obtain ⟨C,hC⟩ := Set.nonempty_iff_ne_empty.mpr hn
  obtain ⟨hx,x,rfl⟩ := hC
  let f : Set V → V := fun C => if hc : C ∈ infiniteClusters G ω then
    Classical.choose hc.2 else x
  have hf (C : Set V) (hC : C ∈ infiniteClusters G ω) : C = cluster G ω (f C) := by
    simp only [f,dite_eq_left hC]
    exact Classical.choose_spec hC.2
  let R : Finset V := hfin.toFinset.image f
  apply hω x R ⟨hx,?_⟩
  intro y hy
  have hc : cluster G ω y ∈ infiniteClusters G ω := ⟨hy,y,rfl⟩
  refine ⟨f (cluster G ω y),Finset.mem_image.mpr ⟨_,hfin.mem_toFinset.mpr hc,rfl⟩,?_⟩
  have he := hf _ hc
  exact (Set.ext_iff.mp he _).mpr (mem_cluster_self G ω (f (cluster G ω y)))

end Percolation

end OAI
