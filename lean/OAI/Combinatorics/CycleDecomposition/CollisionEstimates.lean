import OAI.Combinatorics.CycleDecomposition.Pairing

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} [Fintype V] (G : SimpleGraph V)

def neighborsIn (X : Finset V) (v : V) : ℕ :=
  (X.filter (G.Adj v)).card

def internalGraph (X : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ X ∧ v ∈ X
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma neighborsIn_le_degree (X : Finset V) (v : V) :
    neighborsIn G X v ≤ G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma neighborsIn_eq_sum {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] (G : SimpleGraph V) (X : Finset V) (v : V) :
    neighborsIn G X v = ∑ x ∈ X, if G.Adj v x then 1 else 0 := by
  classical
  simp only [neighborsIn,Finset.card_eq_sum_ones,Finset.sum_filter]

lemma sum_incidence_to_set (X : Finset V) :
    ∑ v, neighborsIn G X v = ∑ x ∈ X, G.degree x := by
  classical
  simp_rw [neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [G.adj_comm (v:=x)]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by
    ext y
    simp
  simp [he]

lemma internalGraph_degree (X : Finset V) (v : V) :
    (internalGraph G X).degree v = if v ∈ X then neighborsIn G X v else 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v ∈ X
  · simp only [hv,ite_true]
    congr 1
    ext x
    rw [SimpleGraph.mem_neighborFinset,Finset.mem_filter]
    change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ _
    tauto
  · have he : (internalGraph G X).neighborFinset v = ∅ := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.notMem_empty]
      change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ False
      tauto
    simp [he,hv]

lemma internalGraph_degree_sum (X : Finset V) :
    2 * (internalGraph G X).edgeFinset.card = ∑ x ∈ X, neighborsIn G X x := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [internalGraph_degree]
  simp

lemma internal_edge_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    2 * ((internalGraph G X).edgeFinset.card : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (internalGraph_degree_sum G X)
  push_cast at hid
  rw [hid]
  calc
    _ ≤ ∑ x ∈ X, a := Finset.sum_le_sum fun x hx =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X x)).trans (ha x hx)
    _ = _ := by simp [mul_comm]

lemma incidence_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    (∑ v, neighborsIn G X v : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (sum_incidence_to_set G X)
  push_cast at hid
  rw [hid]
  simpa [mul_comm] using Finset.sum_le_sum (s:=X) (fun x hx => ha x hx)

lemma wedge_count_bound (X : Finset V) (a : ℝ) (ha : 1 ≤ a)
    (hdegree : ∀ x ∈ X, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G X v : ℝ) ≤ a) :
    ((∑ v, (neighborsIn G X v).choose 2 : ℕ) : ℝ) ≤
      a*(a-1)*X.card/2 := by
  have hb (v : V) : ((neighborsIn G X v).choose 2 : ℝ) ≤
      (a-1)*(neighborsIn G X v)/2 := by
    rw [Nat.cast_choose_two]
    have hn : (0:ℝ) ≤ neighborsIn G X v := Nat.cast_nonneg _
    have hn' := hneighbor v
    nlinarith
  calc
    _ = ∑ v, ((neighborsIn G X v).choose 2 : ℝ) := by push_cast; rfl
    _ ≤ ∑ v, (a-1)*(neighborsIn G X v)/2 := Finset.sum_le_sum fun v _ => hb v
    _ = (a-1)/2 * ∑ v, (neighborsIn G X v : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (a-1)/2 * (a*X.card) := mul_le_mul_of_nonneg_left
        (incidence_bound G X a hdegree) (by positivity)
    _ = _ := by ring

def betweenCount (X Y : Finset V) : ℕ := ∑ x ∈ X, neighborsIn G Y x

lemma betweenCount_comm (X Y : Finset V) :
    betweenCount G X Y = betweenCount G Y X := by
  classical
  simp only [betweenCount,neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  simp only [G.adj_comm]

lemma betweenCount_bound (X Y : Finset V) (a : ℝ)
    (hdegree : ∀ y ∈ Y, (G.degree y : ℝ) ≤ a) :
    (betweenCount G X Y : ℝ) ≤ a*Y.card := by
  rw [betweenCount_comm]
  simp only [betweenCount,Nat.cast_sum]
  calc
    _ ≤ ∑ y ∈ Y, a := Finset.sum_le_sum fun y hy =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X y)).trans (hdegree y hy)
    _ = _ := by simp [mul_comm]

lemma disjoint_neighbor_sum_le {I : Type cycleUniverse3} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (v : V) :
    ∑ i, neighborsIn G (X i) v ≤ G.degree v := by
  classical
  have hb : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (X i).filter (G.Adj v)) := by
    intro i hi j hj hij
    exact (hd hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [neighborsIn]
  rw [← Finset.card_biUnion hb,← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma betweenCount_row_bound {I : Type cycleUniverse4} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (i : I) (a : ℝ)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    (∑ j, betweenCount G (X i) (X j) : ℝ) ≤ a*(X i).card := by
  simp only [betweenCount,Nat.cast_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ X i, a := by
      apply Finset.sum_le_sum
      intro x hx
      have hn := disjoint_neighbor_sum_le G X hd x
      have hn' : (∑ j, (neighborsIn G (X j) x : ℝ)) ≤ G.degree x := by
        exact_mod_cast hn
      exact hn'.trans (hdegree x hx)
    _ = _ := by simp [mul_comm]

lemma cross_error_row {I : Type cycleUniverse5} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 0 ≤ a)
    (hsize : ∀ i, 0 < (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) (i : I) :
    (∑ j, ((betweenCount G (X i) (X j) : ℝ)^2 /
      ((X i).card*(X j).card))) ≤ a^2 := by
  have hmi : (0:ℝ) < (X i).card := by exact_mod_cast hsize i
  calc
    _ ≤ ∑ j, a/(X i).card * (betweenCount G (X i) (X j) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmj : (0:ℝ) < (X j).card := by exact_mod_cast hsize j
      have he := betweenCount_bound G (X i) (X j) a (hdegree j)
      have hn : (0:ℝ) ≤ betweenCount G (X i) (X j) := Nat.cast_nonneg _
      apply (div_le_iff₀ (mul_pos hmi hmj)).mpr
      field_simp
      nlinarith
    _ = a/(X i).card * ∑ j, (betweenCount G (X i) (X j) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ a/(X i).card * (a*(X i).card) := mul_le_mul_of_nonneg_left
      (betweenCount_row_bound G X hd i a (hdegree i)) (by positivity)
    _ = a^2 := by field_simp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

def CollisionPairs {α : Type cycleUniverse6} {β : Type cycleUniverse7} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) : Finset (Finset α) := by
  classical
  exact (s.powersetCard 2).filter (fun p => (p.image f).card = 1)

lemma mem_collisionPairs {α : Type cycleUniverse8} {β : Type cycleUniverse9} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (p : Finset α) :
    p ∈ CollisionPairs f s ↔ p ⊆ s ∧ p.card = 2 ∧ (p.image f).card = 1 := by
  classical
  simp [CollisionPairs,and_assoc]

lemma collisionPairs_mono {α : Type cycleUniverse10} {β : Type cycleUniverse11} [DecidableEq α] [DecidableEq β] (f : α → β) {s t : Finset α} (h : s ⊆ t) :
    CollisionPairs f s ⊆ CollisionPairs f t := by
  classical
  intro p hp
  rw [mem_collisionPairs] at hp ⊢
  exact ⟨hp.1.trans h,hp.2⟩

lemma pair_mem_collisionPairs {α : Type cycleUniverse12} {β : Type cycleUniverse13} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (heq : f a = f b) :
    {a,b} ∈ CollisionPairs f s := by
  classical
  rw [mem_collisionPairs]
  refine ⟨?_,by simp [hne],by simp [heq]⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha
  · exact Finset.mem_singleton.mp hx ▸ hb

theorem prune_collisions {α : Type cycleUniverse14} {β : Type cycleUniverse15} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) :
    ∃ t ⊆ s, Set.InjOn f (t : Set α) ∧ t.image f = s.image f ∧
      s.card - t.card ≤ (CollisionPairs f s).card := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hinj : Set.InjOn f (s : Set α)
  · exact ⟨s,Subset.rfl,hinj,rfl,by simp⟩
  simp only [Set.InjOn,Finset.mem_coe,not_forall] at hinj
  obtain ⟨a,ha,b,hb,heq,hne⟩ := hinj
  have hsub : s.erase a ⊂ s := Finset.erase_ssubset ha
  obtain ⟨t,ht,hinj,himage,hcost⟩ := ih (s.erase a) hsub
  have hpair := pair_mem_collisionPairs f s ha hb hne heq
  have hnot : ({a,b}:Finset α) ∉ CollisionPairs f (s.erase a) := by
    intro hp
    have hh := (mem_collisionPairs f _ _).mp hp
    have := hh.1 (show a ∈ ({a,b}:Finset α) by simp)
    simp at this
  have hlt : (CollisionPairs f (s.erase a)).card < (CollisionPairs f s).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨collisionPairs_mono f (Finset.erase_subset _ _),
      fun he => hnot (he ▸ hpair)⟩
  have himage' : (s.erase a).image f = s.image f := by
    apply le_antisymm
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      by_cases hxa : x = a
      · subst x
        exact Finset.mem_image.mpr ⟨b,by simp [hb,Ne.symm hne],heq.symm⟩
      · exact Finset.mem_image.mpr ⟨x,by simp [hx,hxa],rfl⟩
  refine ⟨t,ht.trans (Finset.erase_subset _ _),hinj,himage.trans himage',?_⟩
  have hcard := Finset.card_erase_of_mem ha
  have htt := Finset.card_le_card ht
  omega

theorem prune_bad_images {α : Type cycleUniverse16} {β : Type cycleUniverse17} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (bad : β → Prop) [DecidablePred bad] :
    ∃ t ⊆ s, (∀ x ∈ t, ¬ bad (f x)) ∧ Set.InjOn f (t : Set α) ∧
      t.image f = (s.filter (fun x => ¬bad (f x))).image f ∧
      s.card-t.card ≤ (s.filter (fun x => bad (f x))).card +
        (CollisionPairs f (s.filter (fun x => ¬bad (f x)))).card := by
  classical
  obtain ⟨t,ht,hinj,himage,hcost⟩ := prune_collisions f (s.filter (fun x => ¬bad (f x)))
  refine ⟨t,ht.trans (Finset.filter_subset _ _),?_,hinj,himage,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp (ht hx)).2
  · have hpart := Finset.card_filter_add_card_filter_not (s:=s) (p:=fun x => bad (f x))
    have hle := Finset.card_le_card ht
    omega

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def quotientDefect {V : Type cycleUniverse18} {W : Type cycleUniverse19} [Fintype V] (G : SimpleGraph V) (projMap : V → W) : ℕ := by
  classical
  let s := G.edgeFinset
  exact (s.filter (fun e => (Sym2.map projMap e).IsDiag)).card +
    (CollisionPairs (Sym2.map projMap) (s.filter (fun e => ¬(Sym2.map projMap e).IsDiag))).card

theorem simple_quotient_representatives {V : Type cycleUniverse20} {W : Type cycleUniverse21} [Fintype V]
    (G : SimpleGraph V) (projMap : V → W) :
    ∃ (retained : Finset (Sym2 V)) (Q : SimpleGraph W),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ quotientDefect G projMap ∧
      Q.edgeSet = ((retained.image (Sym2.map projMap) : Finset (Sym2 W)) : Set (Sym2 W)) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map projMap f = e) := by
  classical
  obtain ⟨t,ht,hgood,hinj,himage,hcost⟩ :=
    prune_bad_images (Sym2.map projMap) G.edgeFinset Sym2.IsDiag
  let Q : SimpleGraph W := SimpleGraph.fromEdgeSet (t.image (Sym2.map projMap) : Set (Sym2 W))
  have hQ : Q.edgeSet = (t.image (Sym2.map projMap) : Set (Sym2 W)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      refine ⟨he,?_⟩
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact hgood f hf
  refine ⟨t,Q,ht,?_,hQ,?_⟩
  · rw [Finset.card_sdiff_of_subset ht]
    exact hcost
  · intro e he
    rw [hQ] at he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
    refine ⟨f,⟨hf,hfe⟩,?_⟩
    intro g hg
    exact hinj hg.1 hf (hg.2.trans hfe.symm)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse22} {I : Type cycleUniverse23} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma familyPaired_symm {V : Type cycleUniverse24} {I : Type cycleUniverse25} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : ∀ i, PairingSpace (X i)) {u v : V}
    (h : familyPaired X p u v) : familyPaired X p v u := by
  obtain ⟨i,hu,hv,hp⟩ := h
  exact ⟨i,hv,hu,paired_symm (p i) hp⟩

lemma familyPaired_local {V : Type cycleUniverse26} {I : Type cycleUniverse27} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    (u v : X i) : familyPaired X p u v ↔ paired (p i) u v := by
  constructor
  · rintro ⟨j,hu,hv,hp⟩
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hd hij) u.property hu
    subst j
    exact hp
  · intro hp
    exact ⟨i,u.property,v.property,hp⟩

lemma familyPaired_same_set {V : Type cycleUniverse28} {I : Type cycleUniverse29} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    {u v : V} (hu : u ∈ X i) (hp : familyPaired X p u v) : v ∈ X i := by
  obtain ⟨j,hu',hv,hp⟩ := hp
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (hd hij) hu hu'
  exact hij.symm ▸ hv

def vertexPairEvent (p : ∀ i, PairingSpace (X i)) (s : Finset V) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ familyPaired X p u v

lemma vertexPairEvent_pair (p : ∀ i, PairingSpace (X i)) (u v : V) (huv : u ≠ v) :
    vertexPairEvent X p {u,v} ↔ familyPaired X p u v := by
  constructor
  · rintro ⟨a,ha,b,hb,hab,hp⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hp
    · exact familyPaired_symm X p hp
    · exact False.elim (hab rfl)
  · intro hp
    exact ⟨u,by simp,v,by simp,huv,hp⟩

lemma finiteAverage_filter_card {Ω : Type cycleUniverse30} {A : Type cycleUniverse31} [Fintype Ω]
    (s : Finset A) (P : Ω → A → Prop) :
    finiteAverage (fun ω => ((s.filter (P ω)).card : ℝ)) =
      ∑ a ∈ s, finiteAverage (fun ω => if P ω a then 1 else 0) := by
  have hf (ω : Ω) : ((s.filter (P ω)).card : ℝ) =
      ∑ a ∈ s, if P ω a then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one,Finset.sum_filter]
  simp_rw [hf]
  exact finiteAverage_sum s _

include hd in
lemma vertexPairEvent_average (i : I) (s : Finset V)
    (hs : s ⊆ X i) (hc : s.card = 2) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if vertexPairEvent X p s then 1 else 0) ≤ 1 / ((X i).card-1:ℝ) := by
  classical
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hc
  have hu := hs (show u ∈ ({u,v}:Finset V) by simp)
  have hv := hs (show v ∈ ({u,v}:Finset V) by simp)
  have he (p : ∀ j, PairingSpace (X j)) :
      vertexPairEvent X p {u,v} ↔ paired (p i) ⟨u,hu⟩ ⟨v,hv⟩ :=
    (vertexPairEvent_pair X p u v huv).trans (familyPaired_local X hd p i ⟨u,hu⟩ ⟨v,hv⟩)
  simp_rw [he]
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if paired p ⟨u,hu⟩ ⟨v,hv⟩ then 1 else 0)]
  convert paired_first_bound (V:=(X i)) (by simpa using hm) ⟨u,hu⟩ ⟨v,hv⟩
    (fun h => huv (congrArg Subtype.val h)) using 1 ; simp

def wedgeErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) (v : V) :=
  (((X i).filter (G.Adj v)).powersetCard 2).filter (vertexPairEvent X p)

include hd in
lemma wedgeErrors_average (G : SimpleGraph V) (i : I) (v : V)
    (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((wedgeErrors X G p i v).card : ℝ)) ≤
      ((neighborsIn G (X i) v).choose 2 : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((((X i).filter (G.Adj v)).powersetCard 2).filter
    (vertexPairEvent X p)).card : ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _s ∈ ((X i).filter (G.Adj v)).powersetCard 2,
        1 / ((X i).card-1:ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hs
      exact vertexPairEvent_average X hd i s (hs.trans (Finset.filter_subset _ _)) hc hm
    _ = _ := by simp [Finset.card_powersetCard,neighborsIn,div_eq_mul_inv]

lemma mem_internalGraph {G : SimpleGraph V} {S : Finset V} {u v : V} :
    s(u,v) ∈ (internalGraph G S).edgeFinset ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  rfl

def crossGraph (G : SimpleGraph V) (S T : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma distinct_edge_cases (G : SimpleGraph V) {e f : Sym2 V}
    (he : e ∈ G.edgeFinset) (hf : f ∈ G.edgeFinset) (hef : e ≠ f) :
    (∃ v u w, v ≠ u ∧ v ≠ w ∧ u ≠ w ∧ e = s(v,u) ∧ f = s(v,w)) ∨
    (∃ u v x y, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      e = s(u,v) ∧ f = s(x,y)) := by
  obtain ⟨a,b⟩ := e
  obtain ⟨c,d⟩ := f
  have hab : a ≠ b := (SimpleGraph.mem_edgeFinset.mp he).ne
  have hcd : c ≠ d := (SimpleGraph.mem_edgeFinset.mp hf).ne
  by_cases hac : a = c
  · subst c
    refine Or.inl ⟨a,b,d,hab,hcd,?_,rfl,rfl⟩
    intro hbd
    exact hef (hbd ▸ rfl)
  by_cases had : a = d
  · subst d
    refine Or.inl ⟨a,b,c,hab,hcd.symm,?_,rfl,Sym2.eq_swap⟩
    intro hbc
    subst c
    exact hef Sym2.eq_swap
  by_cases hbc : b = c
  · subst c
    refine Or.inl ⟨b,a,d,hab.symm,hcd,?_,Sym2.eq_swap,rfl⟩
    intro had
    subst d
    exact hef Sym2.eq_swap
  by_cases hbd : b = d
  · subst d
    refine Or.inl ⟨b,a,c,hab.symm,hcd.symm,?_,Sym2.eq_swap,Sym2.eq_swap⟩
    intro hac
    subst c
    exact hef rfl
  exact Or.inr ⟨a,b,c,d,hab,hcd,hac,had,hbc,hbd,rfl,rfl⟩

lemma internal_collision_average (i : I) (hm : 4 ≤ (X i).card)
    (u v x y : X i) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
  classical
  have hmono : finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if (paired (p i) u x ∧ paired (p i) v y) ∨
        (paired (p i) u y ∧ paired (p i) v x) then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        (fun h => huy (Subtype.ext h)) (fun h => hvx (Subtype.ext h))
        (fun h => hvy (Subtype.ext h)) hc
      have he : (paired (p i) u x ∧ paired (p i) v y) ∨
          (paired (p i) u y ∧ paired (p i) v x) := by
        simpa only [familyPaired_local X hd p i] using hh
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if (paired p u x ∧ paired p v y) ∨ (paired p u y ∧ paired p v x)
      then 1 else 0)]
  simpa only [Fintype.card_coe] using pairing_patterns_internal
    (V:=(X i)) (by simpa using hm) u v x y huv hux huy hvx hvy hxy

lemma cross_collision_average (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card)
    (u x : X i) (v y : X j) (hux : u ≠ x) (hvy : v ≠ y) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
  classical
  have huy : (u:V) ≠ y := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) u.property (h ▸ y.property)
  have hvx : (v:V) ≠ x := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) (h ▸ x.property) v.property
  have hmono : finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if paired (p i) u x ∧ paired (p j) v y then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        huy hvx (fun h => hvy (Subtype.ext h)) hc
      have he : paired (p i) u x ∧ paired (p j) v y := by
        rcases hh with hh | hh
        · exact ⟨(familyPaired_local X hd p i u x).mp hh.1,
            (familyPaired_local X hd p j v y).mp hh.2⟩
        · have hy := familyPaired_same_set X hd p i u.property hh.1
          exact False.elim (Finset.disjoint_left.mp (hd hij) hy y.property)
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  simpa only [Fintype.card_coe] using pairing_patterns_cross_bound
    (V:=fun k => X k) i j hij (by simpa using hi) (by simpa using hj) u x hux v y hvy

end
end ErdosGallai.Batch
end
end
end

end OAI
