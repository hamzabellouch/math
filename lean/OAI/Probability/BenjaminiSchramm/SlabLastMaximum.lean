import OAI.Probability.BenjaminiSchramm.SlabFirstVisit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restricted_connection_measure_symm (I : Set E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G (ω ∩ I) x y} = law p {ω | Conn G (ω ∩ I) y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G _,conn_symm G _⟩

theorem last_height_connection_bound [Countable V] [Countable E]
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (p : unitInterval) (x y : V) (hx : f x ≤ b) (hy : b < f y) :
    law p {ω | Conn G (ω ∩ I) x y} ≤
      ∑' z, if b-R ≤ f z ∧ f z ≤ b then
        law p {ω | Conn G (ω ∩ I) x z} *
          law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | b-R ≤ f v})) z y} else 0 := by
  rw [restricted_connection_measure_symm G I p x y]
  have hj : ∀ e u v, u ∈ G e → v ∈ G e → |(-f v)-(-f u)| ≤ R := by
    intro e u v hu hv
    simpa only [neg_sub_neg,abs_sub_comm] using hjump e u v hu hv
  have hh := first_height_connection_bound G (fun v => -f v) R (-b) hR hj I p y x
    (neg_lt_neg hy) (neg_le_neg hx)
  refine hh.trans_eq (tsum_congr fun z => ?_)
  have hband : (-b ≤ -f z ∧ -f z ≤ -b+R) ↔ (b-R ≤ f z ∧ f z ≤ b) := by
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have hD : {v : V | -f v ≤ -b+R} = {v | b-R ≤ f v} := by
    ext v
    change (-f v ≤ -b+R) ↔ (b-R ≤ f v)
    constructor <;> intro h <;> linarith
  rw [hD]
  by_cases hz : b-R ≤ f z ∧ f z ≤ b
  · rw [ite_eq_left (hband.mpr hz),ite_eq_left hz,
      restricted_connection_measure_symm G _ p y z,restricted_connection_measure_symm G I p z x,
      mul_comm]
  · rw [ite_eq_right (fun h => hz (hband.mp h)),ite_eq_right hz]

lemma conn_max_height_disjoint (f : V → ℝ) (I : Set E) (ω : Set E)
    (x y : V) (hconn : Conn G (ω ∩ I) x y) :
    ∃ z, f x ≤ f z ∧ f y ≤ f z ∧ ω ∈ DisjointOccurrence
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ f z})) x z}
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ f z})) z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G (ω ∩ I) x y).mp hconn
  let p := p₀.toPath.val
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image p.support.toFinset f
    ⟨x,List.mem_toFinset.mpr p.start_mem_support⟩
  have hzp : z ∈ p.support := List.mem_toFinset.mp hz
  have hu (v : V) (hv : v ∈ p.support) : f v ≤ f z := hmax v (List.mem_toFinset.mpr hv)
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G (ω ∩ I) (p.takeUntil z hzp)
  obtain ⟨c,hc,hec,hoc⟩ := walk_lift_bonds G (ω ∩ I) (p.dropUntil z hzp)
  have haI : (a.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ f z} := by
    intro e he
    refine ⟨(hoa e (List.mem_toFinset.mp he)).2,fun v hv => ?_⟩
    have hGe : G e ∈ (p.takeUntil z hzp).edges := hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)
    exact hu v (p.support_takeUntil_subset_support hzp (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv))
  have hcI : (c.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ f z} := by
    intro e he
    refine ⟨(hoc e (List.mem_toFinset.mp he)).2,fun v hv => ?_⟩
    have hGe : G e ∈ (p.dropUntil z hzp).edges := hec ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)
    exact hu v (p.support_dropUntil_subset_support hzp (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv))
  refine ⟨z,hu x p.start_mem_support,hu y p.end_mem_support,a.toFinset,c.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he
    exact (hoa e (List.mem_toFinset.mp he)).1
  · intro e he
    exact (hoc e (List.mem_toFinset.mp he)).1
  · apply Finset.disjoint_left.mpr
    intro e heA heC
    exact List.disjoint_left.mp (p₀.toPath.property.isTrail.disjoint_edges_takeUntil_dropUntil hzp)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp heA))
      (hec ▸ List.mem_map_of_mem (List.mem_toFinset.mp heC))
  · have hh := ha.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (a.toFinset : Set E) ⊆ (a.toFinset : Set E) ∩
        (I ∩ internalEdges G {v | f v ≤ f z}) := fun e he => ⟨he,haI he⟩
    exact conn_mono G hsub hh
  · have hh := hc.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (c.toFinset : Set E) ⊆ (c.toFinset : Set E) ∩
        (I ∩ internalEdges G {v | f v ≤ f z}) := fun e he => ⟨he,hcI he⟩
    exact conn_mono G hsub hh

theorem max_height_connection_bound [Countable V] [Countable E]
    (f : V → ℝ) (I : Set E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G (ω ∩ I) x y} ≤
      ∑' z, if f x ≤ f z ∧ f y ≤ f z then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ f z})) x z} *
          law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ f z})) z y} else 0 := by
  let J (z : V) := I ∩ internalEdges G {v | f v ≤ f z}
  let C := fun z => if f x ≤ f z ∧ f y ≤ f z then
    DisjointOccurrence {ω | Conn G (ω ∩ J z) x z} {ω | Conn G (ω ∩ J z) z y} else ∅
  have hsub : {ω | Conn G (ω ∩ I) x y} ⊆ ⋃ z, C z := by
    intro ω hω
    obtain ⟨z,hzx,hzy,hd⟩ := conn_max_height_disjoint G f I ω x y hω
    have hband : f x ≤ f z ∧ f y ≤ f z := ⟨hzx,hzy⟩
    exact Set.mem_iUnion.mpr ⟨z,by simpa only [C,ite_eq_left hband] using hd⟩
  calc
    _ ≤ law p (⋃ z, C z) := measure_mono hsub
    _ ≤ ∑' z, law p (C z) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f x ≤ f z ∧ f y ≤ f z
      · simp only [C,ite_eq_left hz]
        exact bk_ennreal p _ _
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (finiteWitness_conn_restricted G (J z) x z) (finiteWitness_conn_restricted G (J z) z y)
      · simp only [C,ite_eq_right hz,measure_empty,le_refl]

end Percolation.BenjaminiSchramm

end

end OAI
