import OAI.Probability.BenjaminiSchramm.SlabSecondMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma walk_endpoint_height_bound {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v-f u| ≤ R)
    {x y : V} (p : H.Walk x y) (hx : f x < b)
    (hbelow : ∀ v ∈ p.support, v ≠ y → f v < b) : f y ≤ b+R := by
  induction p with
  | nil => linarith
  | @cons x v y hxv p ih =>
    by_cases hv : v = y
    · subst v
      have hh := (abs_le.mp (hjump hxv)).2
      linarith
    · exact ih (hbelow v (by simp) hv)
        (fun w hw hwy => hbelow w (List.mem_cons_of_mem _ hw) hwy)

variable {V E : Type*} (G : BondGraph V E)

lemma conn_first_height_disjoint (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (ω : Set E) (x y : V) (hx : f x < b) (hy : b ≤ f y)
    (hconn : Conn G (ω ∩ I) x y) :
    ∃ z, b ≤ f z ∧ f z ≤ b+R ∧ ω ∈ DisjointOccurrence
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z}
      {η | Conn G (η ∩ I) z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G (ω ∩ I) x y).mp hconn
  let p := p₀.toPath.val
  let S := p.support.toFinset.filter fun v => b ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : b ≤ f z := (Finset.mem_filter.mp hzS).2
  have hbelow (v : V) (hv : v ∈ (p.takeUntil z hzp).support) (hvz : v ≠ z) : f v < b := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  have hj {u v : V} (huv : (openSimpleGraph G (ω ∩ I)).Adj u v) : |f v-f u| ≤ R := by
    obtain ⟨e,_he,heq⟩ := huv.2
    exact hjump e u v (by rw [heq]; simp) (by rw [heq]; simp)
  have hzR : f z ≤ b+R := walk_endpoint_height_bound f R b hR hj (p.takeUntil z hzp) hx hbelow
  have hupper (v : V) (hv : v ∈ (p.takeUntil z hzp).support) : f v ≤ b+R := by
    by_cases hvz : v=z
    · simpa only [hvz] using hzR
    · have hh := hbelow v hv hvz
      linarith
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G (ω ∩ I) (p.takeUntil z hzp)
  obtain ⟨c,hc,hec,hoc⟩ := walk_lift_bonds G (ω ∩ I) (p.dropUntil z hzp)
  have hain (e : E) (he : e ∈ a) : e ∈ internalEdges G {v | f v ≤ b+R} := by
    intro v hv
    have hGe : G e ∈ (p.takeUntil z hzp).edges := hea ▸ List.mem_map_of_mem he
    exact hupper v (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv)
  have haI : (a.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ b+R} := by
    intro e he
    exact ⟨(hoa e (List.mem_toFinset.mp he)).2,hain e (List.mem_toFinset.mp he)⟩
  have hcI : (c.toFinset : Set E) ⊆ I := fun e he => (hoc e (List.mem_toFinset.mp he)).2
  refine ⟨z,hz,hzR,a.toFinset,c.toFinset,?_,?_,?_,?_,?_⟩
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
        (I ∩ internalEdges G {v | f v ≤ b+R}) := fun e he => ⟨he,haI he⟩
    exact conn_mono G hsub hh
  · have hh := hc.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (c.toFinset : Set E) ⊆ (c.toFinset : Set E) ∩ I := fun e he => ⟨he,hcI he⟩
    exact conn_mono G hsub hh

theorem first_height_connection_bound [Countable V] [Countable E]
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (p : unitInterval) (x y : V) (hx : f x < b) (hy : b ≤ f y) :
    law p {ω | Conn G (ω ∩ I) x y} ≤
      ∑' z, if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} *
          law p {ω | Conn G (ω ∩ I) z y} else 0 := by
  let J := I ∩ internalEdges G {v | f v ≤ b+R}
  let C := fun z => if b ≤ f z ∧ f z ≤ b+R then
    DisjointOccurrence {ω | Conn G (ω ∩ J) x z} {ω | Conn G (ω ∩ I) z y} else ∅
  have hsub : {ω | Conn G (ω ∩ I) x y} ⊆ ⋃ z, C z := by
    intro ω hω
    obtain ⟨z,hz,hzR,hd⟩ := conn_first_height_disjoint G f R b hR hjump I ω x y hx hy hω
    have hband : b ≤ f z ∧ f z ≤ b+R := ⟨hz,hzR⟩
    exact Set.mem_iUnion.mpr ⟨z,by simpa only [C,ite_eq_left hband] using hd⟩
  calc
    _ ≤ law p (⋃ z, C z) := measure_mono hsub
    _ ≤ ∑' z, law p (C z) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : b ≤ f z ∧ f z ≤ b+R
      · simp only [C,ite_eq_left hz]
        exact bk_ennreal p _ _
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (finiteWitness_conn_restricted G J x z) (finiteWitness_conn_restricted G I z y)
      · simp only [C,ite_eq_right hz,measure_empty,le_refl]

theorem first_height_layer_moment_bound [Countable V] [Countable E]
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (A : Set V) (p : unitInterval) (x : V)
    (hx : f x < b) (hA : ∀ y ∈ A, b ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      ∑' z, (if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G I A ω z ∂law p) := by
  simp_rw [lintegral_restrictedLayerCount]
  calc
    _ ≤ ∑' y, ∑' z, (if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} else 0) *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) z y} else 0) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y ∈ A
      · simp only [ite_eq_left hy]
        have hh := first_height_connection_bound G f R b hR hjump I p x y hx (hA y hy)
        refine hh.trans_eq (tsum_congr fun z => ?_)
        by_cases hz : b ≤ f z ∧ f z ≤ b+R
        · rw [ite_eq_left hz,ite_eq_left hz]
        · rw [ite_eq_right hz,ite_eq_right hz,zero_mul]
      · simp only [ite_eq_right hy]
        exact bot_le
    _ = _ := by
      rw [ENNReal.tsum_comm]
      congr 1
      funext z
      exact ENNReal.tsum_mul_left

end Percolation.BenjaminiSchramm

end

end OAI
