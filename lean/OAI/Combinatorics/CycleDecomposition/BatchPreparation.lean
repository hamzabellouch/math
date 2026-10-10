import OAI.Combinatorics.CycleDecomposition.CollisionEstimates

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34

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
variable {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma crossGraph_card (G : SimpleGraph V) (S T : Finset V) (hst : Disjoint S T) :
    (crossGraph G S T).edgeFinset.card = betweenCount G S T := by
  classical
  have hdeg (v : V) : (crossGraph G S T).degree v =
      (if v ∈ S then neighborsIn G T v else 0) +
      (if v ∈ T then neighborsIn G S v else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hfin : (crossGraph G S T).neighborFinset v =
      (if v ∈ S then T.filter (G.Adj v) else ∅) ∪
      (if v ∈ T then S.filter (G.Adj v) else ∅) := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union]
      change (G.Adj v x ∧ ((v ∈ S ∧ x ∈ T) ∨ (v ∈ T ∧ x ∈ S))) ↔ _
      split_ifs <;> simp_all only [Finset.mem_filter,Finset.notMem_empty] <;> tauto
    rw [hfin,Finset.card_union_of_disjoint]
    · split_ifs <;> simp [neighborsIn]
    · split_ifs with hs ht ht
      · exact False.elim (Finset.disjoint_left.mp hst hs ht)
      all_goals simp
  have hh := (crossGraph G S T).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hh
  rw [Finset.sum_add_distrib] at hh
  have hS : (∑ v, if v ∈ S then neighborsIn G T v else 0) = betweenCount G S T := by
    simp [betweenCount]
  have hT : (∑ v, if v ∈ T then neighborsIn G S v else 0) = betweenCount G T S := by
    simp [betweenCount]
  rw [hS,hT,betweenCount_comm G T S] at hh
  omega

def edgePairEvent (p : ∀ i, PairingSpace (X i)) (q : Finset (Sym2 V)) : Prop :=
  (q.image (Sym2.map (familyProject X hd p))).card = 1

lemma edgePairEvent_pair (p : ∀ i, PairingSpace (X i)) (e f : Sym2 V) :
    edgePairEvent X hd p {e,f} ↔
      Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f := by
  classical
  by_cases h : Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f
  · simp [edgePairEvent,h]
  · simp [edgePairEvent,h,Finset.card_pair h]

def DisjointEdgePair (q : Finset (Sym2 V)) : Prop :=
  ∃ u v x y : V, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
    q = {s(u,v),s(x,y)}

def pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :=
  ((H.edgeFinset.powersetCard 2).filter DisjointEdgePair).filter (edgePairEvent X hd p)

def loopErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) :=
  (internalGraph G (X i)).edgeFinset.filter
    (fun e => (Sym2.map (familyProject X hd p) e).IsDiag)

lemma loopErrors_average (G : SimpleGraph V) (i : I) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((loopErrors X hd G p i).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((internalGraph G (X i)).edgeFinset.filter _).card:ℝ)) ≤ _
  have hav := finiteAverage_filter_card (s:=(internalGraph G (X i)).edgeFinset)
    (P:=fun (p : ∀ j, PairingSpace (X j)) e => (Sym2.map (familyProject X hd p) e).IsDiag)
  calc
    _ = ∑ e ∈ (internalGraph G (X i)).edgeFinset,
        finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
          if (Sym2.map (familyProject X hd p) e).IsDiag then 1 else 0) := by
      convert hav using 1 <;> congr 4
      · funext p
        congr 2
        ext e
        simp only [Finset.mem_filter]
      · funext e
        congr 1
        funext p
        split_ifs <;> rfl
    _ ≤ _ := by
      calc
        _ ≤ ∑ _e ∈ (internalGraph G (X i)).edgeFinset, 1 / ((X i).card-1:ℝ) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨u,v⟩ := e
          obtain ⟨huv,hu,hv⟩ := mem_internalGraph.mp he
          have heq (p : ∀ j, PairingSpace (X j)) :
              (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ vertexPairEvent X p {u,v} :=
            (loop_iff_familyPaired X hd p huv.ne).trans (vertexPairEvent_pair X p u v huv.ne).symm
          simp_rw [heq]
          exact vertexPairEvent_average X hd i {u,v} (by intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz; exact hu; exact Finset.mem_singleton.mp hz ▸ hv)
            (by simp [huv.ne]) hm
        _ = _ := by simp [div_eq_mul_inv]

lemma internal_pairErrors_average (G : SimpleGraph V) (i : I) (hm : 4 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card.choose 2 : ℝ) *
        (2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
      have hsub := (Finset.mem_powersetCard.mp hq).1
      obtain ⟨he,hu,hv⟩ := mem_internalGraph.mp (hsub (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      obtain ⟨hf,hx,hy⟩ := mem_internalGraph.mp (hsub (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      simp_rw [edgePairEvent_pair]
      exact internal_collision_average X hd i hm ⟨u,hu⟩ ⟨v,hv⟩ ⟨x,hx⟩ ⟨y,hy⟩
        (fun h => huv (congrArg Subtype.val h)) (fun h => hux (congrArg Subtype.val h))
        (fun h => huy (congrArg Subtype.val h)) (fun h => hvx (congrArg Subtype.val h))
        (fun h => hvy (congrArg Subtype.val h)) (fun h => hxy (congrArg Subtype.val h))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (4:ℝ) ≤ (X i).card := by exact_mod_cast hm
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

lemma cross_pair_orientation {V : Type cycleUniverse3} {I : Type cycleUniverse4} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (G : SimpleGraph V) (i j : I)
    (q : Finset (Sym2 V)) (hq : q ⊆ (crossGraph G (X i) (X j)).edgeFinset)
    (hdis : DisjointEdgePair q) :
    ∃ (u x : X i) (v y : X j), u ≠ x ∧ v ≠ y ∧ q = {s((u:V),(v:V)),s((x:V),(y:V))} := by
  classical
  obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
  have he := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  have hf := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  rcases he.2 with ⟨hui,hvj⟩ | ⟨huj,hvi⟩ <;> rcases hf.2 with ⟨hxi,hyj⟩ | ⟨hxj,hyi⟩
  · exact ⟨⟨u,hui⟩,⟨x,hxi⟩,⟨v,hvj⟩,⟨y,hyj⟩,
      (fun h => hux (congrArg Subtype.val h)),(fun h => hvy (congrArg Subtype.val h)),rfl⟩
  · refine ⟨⟨u,hui⟩,⟨y,hyi⟩,⟨v,hvj⟩,⟨x,hxj⟩,
      (fun h => huy (congrArg Subtype.val h)),(fun h => hvx (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=y) (b:=x)]
  · refine ⟨⟨v,hvi⟩,⟨x,hxi⟩,⟨u,huj⟩,⟨y,hyj⟩,
      (fun h => hvx (congrArg Subtype.val h)),(fun h => huy (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u)]
  · refine ⟨⟨v,hvi⟩,⟨y,hyi⟩,⟨u,huj⟩,⟨x,hxj⟩,
      (fun h => hvy (congrArg Subtype.val h)),(fun h => hux (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u),Sym2.eq_swap (a:=y) (b:=x)]

lemma cross_pairErrors_average (G : SimpleGraph V) (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      ((betweenCount G (X i) (X j)).choose 2 : ℝ) *
        (1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,x,v,y,hux,hvy,rfl⟩ := cross_pair_orientation X G i j q
        (Finset.mem_powersetCard.mp hq).1 hdis
      simp_rw [edgePairEvent_pair]
      exact cross_collision_average X hd i j hij hi hj u x v y hux hvy
    _ ≤ _ := by
      rw [← crossGraph_card G (X i) (X j) (hd hij)]
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (2:ℝ) ≤ (X i).card := by exact_mod_cast hi
        have : (2:ℝ) ≤ (X j).card := by exact_mod_cast hj
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse5} {I : Type cycleUniverse6} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma mem_pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    (q : Finset (Sym2 V)) :
    q ∈ pairErrors X hd H p ↔ q ⊆ H.edgeFinset ∧ q.card = 2 ∧
      DisjointEdgePair q ∧ edgePairEvent X hd p q := by
  classical
  simp [pairErrors,and_assoc]

lemma mem_crossGraph {G : SimpleGraph V} {S T : Finset V} {u v : V} :
    s(u,v) ∈ (crossGraph G S T).edgeFinset ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S)) := by
  rw [SimpleGraph.mem_edgeFinset]
  rfl

lemma two_paired_edges_placement (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    {u v x y : V} (he : G.Adj u v) (hf : G.Adj x y)
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
    (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
  classical
  rcases paired_fibers_placement X p hux hvy with ⟨i,hu,hv,hx,hy⟩ | ⟨i,j,hij,hu,hx,hv,hy⟩
  · left
    refine ⟨i,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_internalGraph.mpr ⟨he,hu,hv⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_internalGraph.mpr ⟨hf,hx,hy⟩
  · right
    refine ⟨i,j,hij,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_crossGraph.mpr ⟨he,Or.inl ⟨hu,hv⟩⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_crossGraph.mpr ⟨hf,Or.inl ⟨hx,hy⟩⟩

def wedgeCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun v =>
    (wedgeErrors X G p i v).image (fun q => q.image (fun u => s(v,u)))

def internalCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => pairErrors X hd (internalGraph G (X i)) p

def crossCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => (Finset.univ.erase i).biUnion fun j =>
    pairErrors X hd (crossGraph G (X i) (X j)) p

lemma all_collisions_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    CollisionPairs (Sym2.map (familyProject X hd p)) G.edgeFinset ⊆
      wedgeCover X G p ∪ internalCover X hd G p ∪ crossCover X hd G p := by
  classical
  intro q hq
  obtain ⟨hsub,hcard,himage⟩ := (mem_collisionPairs _ _ _).mp hq
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hcard
  have he := hsub (by simp : e ∈ ({e,f}:Finset (Sym2 V)))
  have hf := hsub (by simp : f ∈ ({e,f}:Finset (Sym2 V)))
  have hev : edgePairEvent X hd p {e,f} := himage
  have heq := (edgePairEvent_pair X hd p e f).mp hev
  rcases distinct_edge_cases G he hf hef with hshared | hdis
  · obtain ⟨v,u,w,hvu,hvw,huw,rfl,rfl⟩ := hshared
    have hpair := shared_endpoint_collision X hd p huw heq
    obtain ⟨i,hu,hw,hpair'⟩ := hpair
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨{u,w},?_,by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,by simp [huw]⟩,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_filter.mpr ⟨hu,SimpleGraph.mem_edgeFinset.mp he⟩
      · exact Finset.mem_singleton.mp hz ▸ Finset.mem_filter.mpr ⟨hw,SimpleGraph.mem_edgeFinset.mp hf⟩
    · exact (vertexPairEvent_pair X p u w huw).mpr ⟨i,hu,hw,hpair'⟩
  · obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl,rfl⟩ := hdis
    have hdis : DisjointEdgePair ({s(u,v),s(x,y)}:Finset (Sym2 V)) :=
      ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩
    have hplace : (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
        (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
      rcases four_endpoint_collision X hd p hux huy hvx hvy heq with hh | hh
      · exact two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf) hh.1 hh.2
      · have hh' := two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf).symm hh.1 hh.2
        simpa only [Sym2.eq_swap (a:=y) (b:=x)] using hh'
    rcases hplace with ⟨i,hi⟩ | ⟨i,j,hij,hij'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
        (mem_pairErrors X hd _ p _).mpr ⟨hi,by simp [hef],hdis,hev⟩⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,by simp [hij.symm],?_⟩⟩
      exact (mem_pairErrors X hd _ p _).mpr ⟨hij',by simp [hef],hdis,hev⟩

lemma all_loops_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    G.edgeFinset.filter (fun e => (Sym2.map (familyProject X hd p) e).IsDiag) ⊆
      Finset.univ.biUnion (fun i => loopErrors X hd G p i) := by
  classical
  intro e he
  obtain ⟨he,hloop⟩ := Finset.mem_filter.mp he
  obtain ⟨u,v⟩ := e
  have huv := SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨i,hu,hv,hp⟩ := (loop_iff_familyPaired X hd p huv.ne).mp hloop
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
    Finset.mem_filter.mpr ⟨mem_internalGraph.mpr ⟨huv,hu,hv⟩,hloop⟩⟩

def foldErrorBudget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : ℕ :=
  ∑ i, ((loopErrors X hd G p i).card +
    (∑ v, (wedgeErrors X G p i v).card) +
    (pairErrors X hd (internalGraph G (X i)) p).card +
    ∑ j ∈ Finset.univ.erase i, (pairErrors X hd (crossGraph G (X i) (X j)) p).card)

lemma quotientDefect_le_budget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    quotientDefect G (familyProject X hd p) ≤ foldErrorBudget X hd G p := by
  classical
  have hl := (Finset.card_le_card (all_loops_covered X hd G p)).trans
    (Finset.card_biUnion_le)
  have hc := (Finset.card_le_card (all_collisions_covered X hd G p)).trans
    (Finset.card_union_le _ _)
  have hw : (wedgeCover X G p).card ≤ ∑ i, ∑ v, (wedgeErrors X G p i v).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun v hv => Finset.card_image_le
  have hi : (internalCover X hd G p).card ≤
      ∑ i, (pairErrors X hd (internalGraph G (X i)) p).card := Finset.card_biUnion_le
  have hx : (crossCover X hd G p).card ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
      (pairErrors X hd (crossGraph G (X i) (X j)) p).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun i hi => Finset.card_biUnion_le
  have hc' := Finset.card_le_card (collisionPairs_mono (Sym2.map (familyProject X hd p))
    (Finset.filter_subset (fun e => ¬(Sym2.map (familyProject X hd p) e).IsDiag) G.edgeFinset))
  have hunion := Finset.card_union_le (wedgeCover X G p) (internalCover X hd G p)
  unfold quotientDefect foldErrorBudget
  simp only [Finset.sum_add_distrib]
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma fold_ratio_one (m : ℝ) (hm : 8 ≤ m) : m/(m-1) ≤ 8/7 := by
  apply (div_le_iff₀ (show 0 < m-1 by linarith)).mpr
  linarith
lemma fold_ratio_three (m : ℝ) (hm : 8 ≤ m) : m/(m-3) ≤ 8/5 := by
  apply (div_le_iff₀ (show 0 < m-3 by linarith)).mpr
  linarith
lemma choose_two_real_bound (n : ℕ) : (n.choose 2 : ℝ) ≤ (n:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  have := Nat.cast_nonneg (α:=ℝ) n
  nlinarith

lemma first_error_numeric (m a e : ℝ) (hm : 8 ≤ m) (he : 2*e ≤ a*m) :
    e/(m-1) + (a*(a-1)*m/2)/(m-1) ≤ (4/7)*a^2 := by
  have hp : 0 < m-1 := by linarith
  calc
    _ = (e+a*(a-1)*m/2)/(m-1) := by ring
    _ ≤ (a^2*m/2)/(m-1) := (div_le_div_iff_of_pos_right hp).mpr (by nlinarith)
    _ = (a^2/2)*(m/(m-1)) := by ring
    _ ≤ (a^2/2)*(8/7) := mul_le_mul_of_nonneg_left (fold_ratio_one m hm) (by positivity)
    _ = _ := by ring

lemma internal_error_numeric (m a : ℝ) (e : ℕ) (hm : 8 ≤ m) (ha : 0 ≤ a)
    (he : 2*(e:ℝ) ≤ a*m) :
    (e.choose 2 : ℝ)*(2/((m-1)*(m-3))) ≤ (16/35)*a^2 := by
  have hp : 0 < m-1 := by linarith
  have hp' : 0 < m-3 := by linarith
  have he2 : (e:ℝ)^2 ≤ (a*m/2)^2 := by
    apply sq_le_sq₀ (Nat.cast_nonneg _) (by positivity) |>.mpr
    linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(2/((m-1)*(m-3))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = (e:ℝ)^2/((m-1)*(m-3)) := by ring
    _ ≤ (a*m/2)^2/((m-1)*(m-3)) := div_le_div_of_nonneg_right he2 (by positivity)
    _ = (a^2/4)*((m/(m-1))*(m/(m-3))) := by field_simp ; ring
    _ ≤ (a^2/4)*((8/7)*(8/5)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_three m hm)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma cross_error_numeric (m n : ℝ) (e : ℕ) (hm : 8 ≤ m) (hn : 8 ≤ n) :
    (e.choose 2 : ℝ)*(1/((m-1)*(n-1))) ≤ (32/49)*((e:ℝ)^2/(m*n)) := by
  have hp : 0 < m-1 := by linarith
  have hq : 0 < n-1 := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(1/((m-1)*(n-1))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = ((e:ℝ)^2/(2*m*n))*((m/(m-1))*(n/(n-1))) := by field_simp
    _ ≤ ((e:ℝ)^2/(2*m*n))*((8/7)*(8/7)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_one n hn)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma first_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 1 ≤ a)
    (hm : 8 ≤ (X i).card)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((loopErrors X hd G p i).card : ℝ) + ∑ v, ((wedgeErrors X G p i v).card:ℝ)) ≤
      (4/7)*a^2 := by
  classical
  rw [finiteAverage_add,finiteAverage_sum]
  have hp : 0 < ((X i).card:ℝ)-1 := by
    have : (8:ℝ) ≤ (X i).card := by exact_mod_cast hm
    linarith
  calc
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        ∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ)/((X i).card-1:ℝ) :=
      add_le_add (loopErrors_average X hd G i (by omega))
        (Finset.sum_le_sum fun v _ => wedgeErrors_average X hd G i v (by omega))
    _ = ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ))/((X i).card-1:ℝ) := by rw [Finset.sum_div]
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (a*(a-1)*(X i).card/2)/((X i).card-1:ℝ) := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right (by exact_mod_cast wedge_count_bound G (X i) a ha hdegree hneighbor) hp.le
    _ ≤ _ := first_error_numeric _ _ _ (by exact_mod_cast hm) (internal_edge_bound G (X i) a hdegree)

lemma internal_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : 8 ≤ (X i).card) (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤ (16/35)*a^2 :=
  (internal_pairErrors_average X hd G i (by omega)).trans
    (internal_error_numeric _ _ _ (by exact_mod_cast hm) ha (internal_edge_bound G (X i) a hdegree))

lemma cross_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ∑ j ∈ Finset.univ.erase i, ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      (32/49)*a^2 := by
  classical
  rw [finiteAverage_sum]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hij := (Finset.mem_erase.mp hj).1.symm
      exact (cross_pairErrors_average X hd G i j hij (by have := hm i; omega) (by have := hm j; omega)).trans
        (cross_error_numeric _ _ _ (by exact_mod_cast hm i) (by exact_mod_cast hm j))
    _ ≤ ∑ j, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro j hj hj'
      positivity
    _ = (32/49)*∑ j, ((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cross_error_row G X hd a ha (by intro i; have := hm i; omega) hdegree i) (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse9} {I : Type cycleUniverse10} [Fintype V] [Fintype I]

theorem folding_average_bound (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ)) ≤ 2 * ∑ i, ((X i).card : ℝ) := by
  classical
  simp only [foldErrorBudget,Nat.cast_sum,Nat.cast_add]
  rw [finiteAverage_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [finiteAverage_add,finiteAverage_add]
  have hfirst := first_errors_average X hd G i a ha (hm i) (hdegree i) (hneighbor i)
  have hint := internal_errors_average X hd G i a (by linarith) (hm i) (hdegree i)
  have hcross := cross_errors_average X hd G i a (by linarith) hm hdegree
  calc
    _ ≤ (4/7)*a^2 + (16/35)*a^2 + (32/49)*a^2 :=
      add_le_add (add_le_add hfirst hint) hcross
    _ ≤ 2 * ((X i).card : ℝ) := by nlinarith [hma i,sq_nonneg a]

theorem pair_folding (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    ∃ (p : ∀ i, PairingSpace (X i)) (retained : Finset (Sym2 V))
      (Q : SimpleGraph (FamilyQuotient X p)),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ 2 * ∑ i, (X i).card ∧
      Q.edgeSet = ((retained.image (Sym2.map (familyProject X hd p)) :
         Finset (Sym2 (FamilyQuotient X p))) : Set (Sym2 (FamilyQuotient X p))) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map (familyProject X hd p) f = e) ∧
      Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  classical
  obtain ⟨p,hp⟩ := exists_le_finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ))
  have hcostR := hp.trans (folding_average_bound G X hd a ha hm hma hdegree hneighbor)
  have hcost : foldErrorBudget X hd G p ≤ 2 * ∑ i, (X i).card := by exact_mod_cast hcostR
  obtain ⟨retained,Q,hsub,herr,hQ,hrep⟩ := simple_quotient_representatives G (familyProject X hd p)
  exact ⟨p,retained,Q,hsub,herr.trans ((quotientDefect_le_budget X hd G p).trans hcost),
    hQ,hrep,family_quotient_order X hd p⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V)

def heavyNeighbors (X : Finset V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => a < (neighborsIn G X v : ℝ))

lemma mem_heavyNeighbors (X : Finset V) (a : ℝ) (v : V) :
    v ∈ heavyNeighbors G X a ↔ a < (neighborsIn G X v : ℝ) := by simp [heavyNeighbors]

lemma heavyNeighbors_disjoint_active (X Y : Finset V) (a : ℝ)
    (hY : ∀ v ∈ Y, (G.degree v : ℝ) ≤ a) :
    Disjoint (heavyNeighbors G X a) Y := by
  apply Finset.disjoint_left.mpr
  intro v hv hy
  have h₁ := (mem_heavyNeighbors G X a v).mp hv
  have h₂ : (neighborsIn G X v : ℝ) ≤ G.degree v := by
    exact_mod_cast neighborsIn_le_degree G X v
  exact (not_lt_of_ge (h₂.trans (hY v hy))) h₁

lemma heavyNeighbors_card_le (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hX : ∀ v ∈ X, (G.degree v : ℝ) ≤ a) :
    (heavyNeighbors G X a).card ≤ X.card := by
  have hsum : a * (heavyNeighbors G X a).card ≤
      ∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ) := by
    calc
      _ = ∑ _v ∈ heavyNeighbors G X a, a := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv =>
        ((mem_heavyNeighbors G X a v).mp hv).le
  have hsub : (∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ)) ≤
      ∑ v, (neighborsIn G X v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have htotal : (∑ v, (neighborsIn G X v : ℝ)) ≤ a * X.card := by
    rw [← Nat.cast_sum, sum_incidence_to_set G X, Nat.cast_sum]
    simpa [mul_comm] using Finset.sum_le_sum (s := X) (fun v hv => hX v hv)
  have hh := hsum.trans (hsub.trans htotal)
  have := (mul_le_mul_iff_right₀ ha).mp hh
  exact_mod_cast this

variable {I : Type cycleUniverse12} [Fintype I] (X : I → Finset V)

def heavyDesignated (a : ℝ) (i : I) : SimpleGraph V :=
  crossGraph G (X i) (heavyNeighbors G (X i) a)

lemma heavyDesignated_le {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse14} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (i : I) : heavyDesignated G X a i ≤ G :=
  fun _ _ h => h.1

theorem heavyDesignated_pairwise {V : Type cycleUniverse15} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse16} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hdegree : ∀ i v, v ∈ X i → (G.degree v : ℝ) ≤ a) :
    Pairwise (fun i j => Disjoint (heavyDesignated G X a i).edgeSet
      (heavyDesignated G X a j).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ u v =>
    change G.Adj u v ∧ ((u ∈ X i ∧ v ∈ heavyNeighbors G (X i) a) ∨
      (u ∈ heavyNeighbors G (X i) a ∧ v ∈ X i)) at hei
    change G.Adj u v ∧ ((u ∈ X j ∧ v ∈ heavyNeighbors G (X j) a) ∨
      (u ∈ heavyNeighbors G (X j) a ∧ v ∈ X j)) at hej
    rcases hei.2 with hi | hi <;> rcases hej.2 with hj | hj
    · exact Finset.disjoint_left.mp (hd hij) hi.1 hj.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X j) (X i) a (hdegree i)) hj.1 hi.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X i) (X j) a (hdegree j)) hi.1 hj.1
    · exact Finset.disjoint_left.mp (hd hij) hi.2 hj.2

def trimHeavyGraph (a : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun i hi => h.2 i hi.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma trimHeavyGraph_le {V : Type cycleUniverse17} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse18} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) : trimHeavyGraph G X a ≤ G := fun _ _ h => h.1

theorem trimHeavyGraph_neighbors {V : Type cycleUniverse19} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse20} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (ha : 0 ≤ a) (i : I) (v : V) :
    (neighborsIn (trimHeavyGraph G X a) (X i) v : ℝ) ≤ a := by
  by_cases hv : v ∈ heavyNeighbors G (X i) a
  · have he : (X i).filter ((trimHeavyGraph G X a).Adj v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hui,hvu⟩ := Finset.mem_filter.mp hu
      exact hvu.2 i ⟨hvu.1,Or.inr ⟨hv,hui⟩⟩
    simpa [neighborsIn, he] using ha
  · have hnon : (neighborsIn G (X i) v : ℝ) ≤ a :=
      le_of_not_gt (fun hh => hv ((mem_heavyNeighbors G (X i) a v).mpr hh))
    apply le_trans _ hnon
    exact_mod_cast Finset.card_le_card (show
      (X i).filter ((trimHeavyGraph G X a).Adj v) ⊆ (X i).filter (G.Adj v) from
      fun u hu => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
        (Finset.mem_filter.mp hu).2.1⟩)

theorem trimHeavyGraph_degree (a : ℝ) (v : V) :
    (trimHeavyGraph G X a).degree v ≤ G.degree v := by
  classical
  exact SimpleGraph.degree_le_of_le (trimHeavyGraph_le G X a)

theorem trimHeavyGraph_ledger (a : ℝ) :
    (trimHeavyGraph G X a).edgeSet ∪
      (⋃ i, (heavyDesignated G X a i).edgeSet) = G.edgeSet ∧
    Disjoint (trimHeavyGraph G X a).edgeSet
      (⋃ i, (heavyDesignated G X a i).edgeSet) := by
  constructor
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_union, Set.mem_iUnion, SimpleGraph.mem_edgeSet]
      change (G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v) ∨
        (∃ i, (heavyDesignated G X a i).Adj u v) ↔ G.Adj u v
      constructor
      · rintro (h | ⟨i,hi⟩)
        · exact h.1
        · exact hi.1
      · intro h
        by_cases he : ∃ i, (heavyDesignated G X a i).Adj u v
        · exact Or.inr he
        · exact Or.inl ⟨h,fun i hi => he ⟨i,hi⟩⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hf
      exact he.2 i hi

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

structure TrimmedPath {V : Type cycleUniverse21} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : walk.IsPath

lemma alternating_endpoint_mem {V : Type cycleUniverse22} {G : SimpleGraph V} (X H : Set V)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) :
    (a ∈ X ∨ a ∈ H) ∧ (b ∈ X ∨ b ∈ H) := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  constructor
  · exact (hbi (p.adj_snd hn)).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · exact (hbi (p.adj_penultimate hn)).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

lemma alternating_snd_mem {V : Type cycleUniverse23} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ H) : p.snd ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_snd hn) with h | h
  · exact False.elim (Set.disjoint_left.mp hd h.1 ha)
  · exact h.2

lemma alternating_penultimate_mem {V : Type cycleUniverse24} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (hb : b ∈ H) :
    p.penultimate ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_penultimate hn) with h | h
  · exact h.1
  · exact False.elim (Set.disjoint_left.mp hd h.2 hb)

theorem trim_bipartite_path {V : Type cycleUniverse25} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ q : TrimmedPath G,
      q.walk.edgeSet ⊆ p.edgeSet ∧ p.length ≤ q.walk.length + 2 ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X) := by
  have hends := alternating_endpoint_mem X H hbi p hp
  by_cases ha : a ∈ H
  · have hsa := alternating_snd_mem X H hd hbi p hp ha
    by_cases hb : b ∈ H
    · refine ⟨⟨p.snd,p.tail.penultimate,p.tail.dropLast,hs.tail.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail (List.mem_of_mem_dropLast he)
      · simp only [Walk.length_dropLast,Walk.length_tail]
        omega
      · intro hpos
        have ht : 0 < p.tail.length := by
          change 0 < p.tail.dropLast.length at hpos
          rw [Walk.length_dropLast] at hpos
          omega
        exact ⟨hsa,alternating_penultimate_mem X H hd hbi p.tail ht hb⟩
    · refine ⟨⟨p.snd,b,p.tail,hs.tail⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail he
      · simp only [Walk.length_tail]; omega
      · intro _
        exact ⟨hsa,hends.2.resolve_right hb⟩
  · by_cases hb : b ∈ H
    · refine ⟨⟨a,p.penultimate,p.dropLast,hs.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast] at he ⊢
        exact List.mem_of_mem_dropLast he
      · simp only [Walk.length_dropLast]; omega
      · intro _
        exact ⟨hends.1.resolve_right ha,alternating_penultimate_mem X H hd hbi p hp hb⟩
    · exact ⟨⟨a,b,p,hs⟩,Set.Subset.rfl,by change p.length ≤ p.length + 2; omega,fun _ =>
        ⟨hends.1.resolve_right ha,hends.2.resolve_right hb⟩⟩

lemma bipartite_path_length {V : Type cycleUniverse26} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ X) (hb : b ∈ X) :
    2 ≤ p.length := by
  by_contra h
  have hlen : p.length = 1 := by omega
  rcases hbi (Walk.adj_of_length_eq_one hlen) with he | he
  · exact Set.disjoint_left.mp hd hb he.2
  · exact Set.disjoint_left.mp hd ha he.1

lemma path_edgeFinset_card {V : Type cycleUniverse27} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) : p.edges.toFinset.card = p.length := by
  classical
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

theorem trim_bipartite_path_ledger {V : Type cycleUniverse28} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ (q : TrimmedPath G) (discarded : Finset (Sym2 V)),
      discarded.card ≤ 2 ∧ Disjoint (discarded : Set (Sym2 V)) q.walk.edgeSet ∧
      (discarded : Set (Sym2 V)) ∪ q.walk.edgeSet = p.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X ∧ 2 ≤ q.walk.length) := by
  classical
  obtain ⟨q,hsub,hlen,hends⟩ := trim_bipartite_path X H hd hbi p hs hp
  have hfs : q.walk.edges.toFinset ⊆ p.edges.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp he))
  refine ⟨q,p.edges.toFinset \ q.walk.edges.toFinset,?_,?_,?_,?_⟩
  · rw [Finset.card_sdiff_of_subset hfs, path_edgeFinset_card p hs,
      path_edgeFinset_card q.walk q.simple]
    omega
  · rw [Set.disjoint_left]
    intro e he hq
    exact (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hq)
  · ext e
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, List.mem_toFinset,
      Walk.mem_edgeSet]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hsub h
    · intro h
      by_cases he : e ∈ q.walk.edges
      · exact Or.inr he
      · exact Or.inl ⟨h,he⟩
  · intro hpos
    obtain ⟨ha,hb⟩ := hends hpos
    exact ⟨ha,hb,bipartite_path_length X H hd hbi q.walk hpos ha hb⟩

theorem close_trimmed_path {V : Type cycleUniverse29} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : 2 ≤ p.length)
    (havoid : ∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ p.support) :
    (p.append q).IsCycle ∧ (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  refine ⟨hp.isCycle_append hq ?_ (Or.inl (by omega)), Walk.edgeSet_append p q⟩
  rw [List.disjoint_left]
  intro v hvp hvq
  have hva : v ≠ a := by
    intro h; subst v
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact hn.notMem hvp
  have hvb : v ≠ b := by
    intro h; subst v
    have hn := hq.support_nodup
    rw [← q.cons_tail_support] at hn
    exact hn.notMem hvq
  exact havoid v (List.mem_of_mem_tail hvq) hva hvb (List.mem_of_mem_tail hvp)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpoint_path_count_on {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G) (S : Finset V)
    (hends : ∀ i, (P i).start ∈ S ∧ (P i).finish ∈ S)
    (hload : ∀ v, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ S.card := by
  classical
  have heq : ∑ v ∈ S, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    have hc : ∀ i : I, (∑ v ∈ S, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : S.filter (fun v => (P i).start = v ∨ (P i).finish = v) =
          {(P i).start,(P i).finish} := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
        constructor
        · intro h; simpa only [eq_comm] using h.2
        · intro h
          rcases h with rfl | rfl
          · exact ⟨(hends i).1,Or.inl rfl⟩
          · exact ⟨(hends i).2,Or.inr rfl⟩
      rw [← Finset.sum_filter,hf]
      simp [(P i).endpoints_ne]
    simp_rw [hc]
    simp [mul_comm]
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ S) => hload v)
  rw [heq] at hb
  simp only [Finset.sum_const, smul_eq_mul] at hb
  omega

lemma heavy_paths {V : Type cycleUniverse32} [Fintype V] (G : SimpleGraph V)
    (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ v ∈ X, (G.degree v:ℝ) ≤ a) :
    let H := heavyNeighbors G X a
    let B := crossGraph G X H
    ∃ (k : ℕ) (P : Fin k → PositiveSimplePath B),
      Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = B.edgeSet ∧ k ≤ 2 * X.card := by
  classical
  dsimp only
  obtain ⟨k,P,hd,hu,hl,_⟩ := endpoint_path_partition (crossGraph G X (heavyNeighbors G X a))
  refine ⟨k,P,hd,hu,?_⟩
  have hend : ∀ i, (P i).start ∈ X ∪ heavyNeighbors G X a ∧
      (P i).finish ∈ X ∪ heavyNeighbors G X a := by
    intro i
    have h := alternating_endpoint_mem (X:Set V) (heavyNeighbors G X a : Set V)
      (fun {_ _} (h : (crossGraph G X (heavyNeighbors G X a)).Adj _ _) => h.2) (P i).walk (P i).positive
    exact ⟨Finset.mem_union.mpr h.1,Finset.mem_union.mpr h.2⟩
  have hk := endpoint_path_count_on P (X ∪ heavyNeighbors G X a) hend hl
  rw [Fintype.card_fin] at hk
  have hh := heavyNeighbors_card_le G X a ha hdeg
  exact hk.trans ((Finset.card_union_le _ _).trans (by omega))

lemma folded_order_saving {V : Type cycleUniverse33} {I : Type cycleUniverse34} [Fintype V] [Fintype I]
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : ∀ i, PairingSpace (X i)) (hsize : ∀ i, 2 ≤ (X i).card) :
    (Fintype.card (FamilyQuotient X p):ℝ) ≤ Fintype.card V -
      (1/3:ℝ) * ∑ i, ((X i).card:ℝ) := by
  have he := family_quotient_order_add X hd p
  have hf : ∀ i, ((X i).card:ℝ)/3 ≤ ((X i).card/2:ℕ) := by
    intro i
    have h := Nat.mod_add_div (X i).card 2
    have hm := Nat.mod_lt (X i).card (by decide : 0<2)
    have hs := hsize i
    have hi : (X i).card ≤ 3 * ((X i).card/2) := by omega
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr (by simpa only [mul_comm] using (show ((X i).card:ℝ) ≤ 3*((X i).card/2:ℕ) by exact_mod_cast hi))
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (univ:Finset I)) => hf i)
  have he' : (Fintype.card (FamilyQuotient X p):ℝ) + ∑ i, (((X i).card/2:ℕ):ℝ) =
      Fintype.card V := by exact_mod_cast he
  rw [← Finset.sum_div] at hb
  linarith

structure PreparedBatch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j)) where
  pairing : ∀ i, PairingSpace (X i)
  quotient : SimpleGraph (FamilyQuotient X pairing)
  retained : Finset (Sym2 V)
  bad : Finset (Sym2 V)
  count : I → ℕ
  path : ∀ i, Fin (count i) → TrimmedPath G
  count_le : ∀ i, count i ≤ 2 * (X i).card
  bad_le : bad.card ≤ 6 * ∑ i, (X i).card
  ends : ∀ i j, 0 < (path i j).walk.length →
    (path i j).start ∈ X i ∧ (path i j).finish ∈ X i ∧ 2 ≤ (path i j).walk.length
  paths_disjoint : Pairwise fun z w : Σ i, Fin (count i) =>
    Disjoint (path z.1 z.2).walk.edgeSet (path w.1 w.2).walk.edgeSet
  bad_paths : ∀ i j, Disjoint (bad : Set (Sym2 V)) (path i j).walk.edgeSet
  retained_paths : ∀ i j, Disjoint (retained : Set (Sym2 V)) (path i j).walk.edgeSet
  bad_retained : Disjoint (bad : Set (Sym2 V)) (retained : Set (Sym2 V))
  cover : (bad : Set (Sym2 V)) ∪ (retained : Set (Sym2 V)) ∪
    (⋃ (i) (j), (path i j).walk.edgeSet) = G.edgeSet
  quotient_edges : quotient.edgeSet =
    (Sym2.map (familyProject X hd pairing)) '' (retained : Set (Sym2 V))
  representatives : ∀ e ∈ quotient.edgeSet, ∃! f,
    f ∈ retained ∧ Sym2.map (familyProject X hd pairing) f = e
  order : Fintype.card (FamilyQuotient X pairing) =
    Fintype.card V - ∑ i, (X i).card / 2

lemma PreparedBatch.bad_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.bad : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_left) _

lemma PreparedBatch.retained_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.retained : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_right) _

theorem prepare_batch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (a : ℝ) (ha : 1 ≤ a) (hm : ∀ i, 8 ≤ (X i).card)
    (hma : ∀ i, a^2 ≤ (X i).card)
    (hdeg : ∀ i v, v ∈ X i → (G.degree v:ℝ) ≤ a) :
    Nonempty (PreparedBatch G X hd) := by
  classical
  let H := heavyDesignated G X a
  let T := trimHeavyGraph G X a
  have hHpair := heavyDesignated_pairwise G X a hd hdeg
  have hT := trimHeavyGraph_ledger G X a
  have hpaths : ∀ i, ∃ (k : ℕ) (P : Fin k → PositiveSimplePath (H i)),
      Pairwise (fun j l => Disjoint (P j).walk.edgeSet (P l).walk.edgeSet) ∧
      (⋃ j, (P j).walk.edgeSet) = (H i).edgeSet ∧ k ≤ 2*(X i).card :=
    fun i => heavy_paths G (X i) a (by linarith) (hdeg i)
  choose k P hPd hPu hk using hpaths
  have htrim : ∀ i j, ∃ (q : TrimmedPath (H i)) (S : Finset (Sym2 V)),
      S.card ≤ 2 ∧ Disjoint (S:Set _) q.walk.edgeSet ∧
      (S:Set _) ∪ q.walk.edgeSet = (P i j).walk.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X i ∧ q.finish ∈ X i ∧ 2 ≤ q.walk.length) := by
    intro i j
    exact trim_bipartite_path_ledger (X i:Set V) (heavyNeighbors G (X i) a:Set V)
      (by simpa only [Finset.disjoint_coe] using
        (heavyNeighbors_disjoint_active G (X i) (X i) a (hdeg i)).symm)
      (fun {_ _} (h : (H i).Adj _ _) => h.2) (P i j).walk (P i j).isPath (P i j).positive
  choose q S hSnum hSq hScover hEnds using htrim
  let Qpath : ∀ i, Fin (k i) → TrimmedPath G := fun i j =>
    ⟨(q i j).start,(q i j).finish,(q i j).walk.map (SimpleGraph.Hom.ofLE (heavyDesignated_le G X a i)),
      (q i j).simple.map (Function.injective_id)⟩
  have hQedges : ∀ i j, (Qpath i j).walk.edgeSet = (q i j).walk.edgeSet := by
    intro i j; simp [Qpath,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hQlen : ∀ i j, (Qpath i j).walk.length = (q i j).walk.length :=
    fun i j => Walk.length_map _ _
  have hSsub : ∀ i j, (S i j:Set _) ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [← hScover i j]; exact Set.subset_union_left
  have hqsub : ∀ i j, (Qpath i j).walk.edgeSet ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [hQedges,← hScover i j]; exact Set.subset_union_right
  have hPsub : ∀ i j, (P i j).walk.edgeSet ⊆ (H i).edgeSet :=
    fun i j => (P i j).walk.edges_subset_edgeSet
  have hPdall : Pairwise fun z w : Σ i, Fin (k i) =>
      Disjoint (P z.1 z.2).walk.edgeSet (P w.1 w.2).walk.edgeSet := by
    rintro ⟨i,j⟩ ⟨l,m⟩ hne
    by_cases hi : i = l
    · subst l
      exact hPd i (fun he => hne (by cases he; rfl))
    · exact (hHpair hi).mono (hPsub _ _) (hPsub _ _)
  let B := Finset.univ.biUnion fun z : Σ i, Fin (k i) => S z.1 z.2
  have hB : (B:Set (Sym2 V)) = ⋃ i, ⋃ j, (S i j : Set (Sym2 V)) := by
    ext e; simp [B]
  have hBnum : B.card ≤ 4 * ∑ i, (X i).card := by
    have hc : B.card ≤ ∑ z : Σ i, Fin (k i), (S z.1 z.2).card :=
      Finset.card_biUnion_le
    have hj : (∑ z : Σ i, Fin (k i), (S z.1 z.2).card) ≤ 2 * ∑ i, k i := by
      calc
        _ ≤ ∑ z : Σ i, Fin (k i), 2 := Finset.sum_le_sum (fun z _ => hSnum z.1 z.2)
        _ = _ := by simp [Fintype.card_sigma,mul_comm]
    have hk' := Finset.sum_le_sum (fun i (_:i∈(univ:Finset I)) => hk i)
    rw [← Finset.mul_sum] at hk'
    omega
  have hBheavy : (B:Set (Sym2 V)) ⊆ ⋃ i, (H i).edgeSet := by
    rw [hB]; exact Set.iUnion_subset (fun i => Set.iUnion_subset (fun j =>
      Set.subset_iUnion_of_subset i ((hSsub i j).trans (hPsub i j))))
  have hBhq : ∀ i j, Disjoint (B:Set (Sym2 V)) (Qpath i j).walk.edgeSet := by
    intro i j
    rw [hB,Set.disjoint_iUnion_left]
    intro l
    rw [Set.disjoint_iUnion_left]
    intro m
    by_cases he : (⟨l,m⟩ : Σ i, Fin (k i)) = ⟨i,j⟩
    · cases he
      rw [hQedges]; exact hSq i j
    · exact (hPdall he).mono (hSsub l m) (hqsub i j)
  have hdegT : ∀ i v, v ∈ X i → (T.degree v:ℝ) ≤ a := by
    intro i v hv
    exact (show (T.degree v:ℝ) ≤ G.degree v by exact_mod_cast trimHeavyGraph_degree G X a v).trans (hdeg i v hv)
  obtain ⟨p,R,Q,hR,hBad,hQ,hrep,horder⟩ := pair_folding T X hd a ha hm hma hdegT
    (trimHeavyGraph_neighbors G X a (by linarith))
  let A := T.edgeFinset \ R
  have hA : (A:Set (Sym2 V)) = T.edgeSet \ (R:Set (Sym2 V)) := by
    simp [A,SimpleGraph.coe_edgeFinset]
  have hR' : (R:Set (Sym2 V)) ⊆ T.edgeSet := by
    intro e he; exact SimpleGraph.mem_edgeFinset.mp (hR he)
  refine ⟨⟨p,Q,R,A ∪ B,k,Qpath,hk,?_,?_,?_,?_,?_,?_,?_,?_,hrep,horder⟩⟩
  · exact (Finset.card_union_le _ _).trans (by
      have hn : A.card ≤ 2 * ∑ i, (X i).card := hBad
      omega)
  · intro i j hp
    simpa only [Qpath,Walk.length_map] using hEnds i j (by rwa [hQlen] at hp)
  · intro z w hzw
    exact (hPdall hzw).mono (hqsub _ _) (hqsub _ _)
  · intro i j
    rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hBhq i j⟩
    apply hT.2.mono
    · rw [hA]; exact Set.sdiff_subset
    · exact (hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i))
  · intro i j
    exact hT.2.mono hR' ((hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i)))
  · rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hT.2.symm.mono hBheavy hR'⟩
    rw [hA]; exact Set.disjoint_sdiff_left
  · have hheavy : (B:Set (Sym2 V)) ∪ (⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) =
        ⋃ i, (H i).edgeSet := by
      rw [hB,← Set.iUnion_union_distrib]
      congr 1
      funext i
      rw [← Set.iUnion_union_distrib]
      simp_rw [hQedges,hScover]
      exact hPu i
    rw [Finset.coe_union]
    have hAR : (A:Set (Sym2 V)) ∪ (R:Set (Sym2 V)) = T.edgeSet := by
      rw [hA]; exact Set.sdiff_union_of_subset hR'
    calc
      _ = ((A:Set _) ∪ (R:Set _)) ∪ ((B:Set _) ∪ ⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) := by
        ext e; simp only [Set.mem_union]; tauto
      _ = T.edgeSet ∪ ⋃ i, (H i).edgeSet := by rw [hAR,hheavy]
      _ = G.edgeSet := hT.1
  · simpa only [Finset.coe_image] using hQ

end
end ErdosGallai.Batch
end
end
end

end OAI
