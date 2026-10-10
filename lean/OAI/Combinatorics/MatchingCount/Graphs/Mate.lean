import Mathlib

namespace OAI

namespace MatchingFPRAS.Switching

open Finset
open scoped Classical symmDiff

theorem degree_one_card_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2) :
    (Finset.univ.filter fun v => G.degree v = 1).card ≤ 2 := by
  classical
  have hv := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← G.edgeFinset_card] at hv
  have hs : (∑ v, G.degree v) +
      (Finset.univ.filter fun v => G.degree v = 1).card ≤ 2 * Fintype.card V := by
    calc
      _ = ∑ v, (G.degree v + if G.degree v = 1 then 1 else 0) := by
        simp [Finset.sum_add_distrib]
      _ ≤ ∑ _v : V, 2 := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs with h
        · omega
        · simp only [add_zero]
          exact hd v
      _ = _ := by simp [mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

theorem degree_one_pair {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2)
    (a : V) (ha : G.degree a = 1) :
    ∃ b, b ≠ a ∧ ∀ v, G.degree v = 1 ↔ v = a ∨ v = b := by
  classical
  let s := Finset.univ.filter fun v => G.degree v = 1
  have he : Even s.card := by
    convert G.even_card_odd_degree_vertices using 2
    ext v
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    have := hd v
    interval_cases hdeg : G.degree v <;> norm_num
  have hle : s.card ≤ 2 := degree_one_card_le_two G hc hd
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, by simp [s, ha]⟩
  have hcard : s.card = 2 := by obtain ⟨k, hk⟩ := he; omega
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  have ham : a = x ∨ a = y := by simpa [hs] using (show a ∈ s by simp [s, ha])
  rcases ham with rfl | rfl
  · refine ⟨y, Ne.symm hxy, ?_⟩
    intro v
    have hm : v ∈ s ↔ G.degree v = 1 := by simp [s]
    rw [← hm, hs]
    simp
  · refine ⟨x, hxy, ?_⟩
    intro v
    have hm : v ∈ s ↔ G.degree v = 1 := by simp [s]
    rw [← hm, hs]
    simp [or_comm]

abbrev Mate (V : Type*) := {m : V → V // Function.Involutive m}

variable {V : Type*}

@[simp] theorem mate_mate (m : Mate V) (v : V) : m.1 (m.1 v) = v := m.2 v

def overlay (m n : Mate V) : SimpleGraph V where
  Adj v w := (m.1 v = w ∧ v ≠ w) ∨ (n.1 v = w ∧ v ≠ w)
  symm := ⟨by
    intro v w h
    rcases h with ⟨h, hne⟩ | ⟨h, hne⟩
    · exact Or.inl ⟨by rw [← h, mate_mate], Ne.symm hne⟩
    · exact Or.inr ⟨by rw [← h, mate_mate], Ne.symm hne⟩⟩
  loopless := ⟨by intro v; simp⟩

@[simp] theorem overlay_adj (m n : Mate V) (v w : V) :
    (overlay m n).Adj v w ↔ (m.1 v = w ∧ v ≠ w) ∨ (n.1 v = w ∧ v ≠ w) := Iff.rfl

theorem overlay_comm (m n : Mate V) : overlay m n = overlay n m := by
  ext v w
  exact or_comm

theorem reachable_mate_left (m n : Mate V) (v : V) :
    (overlay m n).Reachable v (m.1 v) := by
  by_cases hv : m.1 v = v
  · rw [hv]
  · exact (show (overlay m n).Adj v (m.1 v) from Or.inl ⟨rfl, Ne.symm hv⟩).reachable

theorem reachable_mate_right (m n : Mate V) (v : V) :
    (overlay m n).Reachable v (n.1 v) := by
  rw [overlay_comm]
  exact reachable_mate_left n m v

theorem reachable_mate_left_iff (m n : Mate V) (a v : V) :
    (overlay m n).Reachable a (m.1 v) ↔ (overlay m n).Reachable a v := by
  constructor
  · intro h
    exact h.trans (reachable_mate_left m n v).symm
  · intro h
    exact h.trans (reachable_mate_left m n v)

theorem reachable_mate_right_iff (m n : Mate V) (a v : V) :
    (overlay m n).Reachable a (n.1 v) ↔ (overlay m n).Reachable a v := by
  rw [overlay_comm]
  exact reachable_mate_left_iff n m a v

noncomputable def switched (m n : Mate V) (a : V) : Mate V := by
  classical
  refine ⟨fun v => if (overlay m n).Reachable a v then n.1 v else m.1 v, ?_⟩
  intro v
  by_cases h : (overlay m n).Reachable a v
  · simp [h, reachable_mate_right_iff]
  · simp [h, reachable_mate_left_iff]

@[simp] theorem switched_apply (m n : Mate V) (a v : V) :
    (switched m n a).1 v =
      if (overlay m n).Reachable a v then n.1 v else m.1 v := by
  classical
  rfl

theorem overlay_switched (m n : Mate V) (a : V) :
    overlay (switched m n a) (switched n m a) = overlay m n := by
  classical
  ext v w
  by_cases h : (overlay m n).Reachable a v <;>
    simp [overlay_adj, switched_apply, overlay_comm n m, h, or_comm]

@[simp] theorem switched_twice (m n : Mate V) (a : V) :
    switched (switched m n a) (switched n m a) a = m := by
  classical
  apply Subtype.ext
  funext v
  by_cases h : (overlay m n).Reachable a v <;>
    simp [overlay_switched, overlay_comm n m, h]

theorem switch_injective (a : V) : Function.Injective
    (fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)) := by
  intro p q h
  have h' := congrArg
    (fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)) h
  simpa using h'

theorem mates_equal_of_adj (m n : Mate V) {v w : V}
    (hvw : (overlay m n).Adj v w) (hv : m.1 v = n.1 v) : m.1 w = n.1 w := by
  rcases hvw with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · rw [mate_mate, hv, mate_mate]
  · rw [← hv, mate_mate, hv, mate_mate]

theorem mates_equal_of_reachable (m n : Mate V) {v w : V}
    (hvw : (overlay m n).Reachable v w) (hv : m.1 v = n.1 v) : m.1 w = n.1 w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw
  induction hvw with
  | refl => exact hv
  | tail h hAdj ih => exact mates_equal_of_adj m n hAdj ih

theorem mates_ne_of_reachable (m n : Mate V) {a v : V}
    (hav : (overlay m n).Reachable a v) (ha : m.1 a ≠ n.1 a) : m.1 v ≠ n.1 v :=
  fun hv => ha (mates_equal_of_reachable m n hav.symm hv)

theorem overlay_degree_le_two [Fintype V] (m n : Mate V) (v : V) :
    (overlay m n).degree v ≤ 2 := by
  classical
  have hs : (overlay m n).neighborFinset v ⊆ {m.1 v, n.1 v} := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset, overlay_adj] at hw
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [← h]
  calc
    _ ≤ ({m.1 v, n.1 v} : Finset V).card := Finset.card_mono hs
    _ ≤ 2 := by
      calc
        _ ≤ ({n.1 v} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp

theorem overlay_degree_one_iff [Fintype V] (m n : Mate V) (v : V)
    (hne : m.1 v ≠ n.1 v) :
    (overlay m n).degree v = 1 ↔ m.1 v = v ∨ n.1 v = v := by
  classical
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hm : (overlay m n).Adj v (m.1 v) := Or.inl ⟨rfl, Ne.symm hn.1⟩
    have ht : (overlay m n).Adj v (n.1 v) := Or.inr ⟨rfl, Ne.symm hn.2⟩
    exact hne (h.unique hm ht)
  · intro h
    rcases h with hm | hn
    · have hn : n.1 v ≠ v := by intro h; exact hne (hm.trans h.symm)
      refine ⟨n.1 v, Or.inr ⟨rfl, Ne.symm hn⟩, ?_⟩
      intro w hw
      rcases hw with ⟨he, hne'⟩ | ⟨he, _⟩
      · exact (hne' (hm.symm.trans he)).elim
      · exact he.symm
    · have hm : m.1 v ≠ v := by intro h; exact hne (h.trans hn.symm)
      refine ⟨m.1 v, Or.inl ⟨rfl, Ne.symm hm⟩, ?_⟩
      intro w hw
      rcases hw with ⟨he, _⟩ | ⟨he, hne'⟩
      · exact he.symm
      · exact (hne' (hn.symm.trans he)).elim

def restrictMate (m : Mate V) (S : Set V)
    (hS : ∀ v, m.1 v ∈ S ↔ v ∈ S) : Mate S :=
  ⟨fun v => ⟨m.1 v.1, (hS v.1).mpr v.2⟩,
   by intro v; apply Subtype.ext; exact m.2 v.1⟩

@[simp] theorem restrictMate_apply (m : Mate V) (S : Set V)
    (hS : ∀ v, m.1 v ∈ S ↔ v ∈ S) (v : S) :
    ((restrictMate m S hS).1 v).1 = m.1 v.1 := rfl

theorem overlay_restrict (m n : Mate V) (S : Set V)
    (hm : ∀ v, m.1 v ∈ S ↔ v ∈ S) (hn : ∀ v, n.1 v ∈ S ↔ v ∈ S) :
    overlay (restrictMate m S hm) (restrictMate n S hn) = (overlay m n).induce S := by
  ext v w
  simp [overlay_adj, SimpleGraph.induce, SimpleGraph.comap, Subtype.ext_iff]

@[simp] theorem component_mem_iff (m n : Mate V) (a v : V) :
    v ∈ ((overlay m n).connectedComponentMk a).supp ↔ (overlay m n).Reachable a v := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    SimpleGraph.reachable_comm]

theorem active_component_endpoints [Fintype V] (m n : Mate V) (a : V)
    (hma : m.1 a = a) (hna : n.1 a ≠ a) :
    ∃ b : V, b ≠ a ∧ (overlay m n).Reachable a b ∧
      ∀ v, (overlay m n).Reachable a v →
        ((m.1 v = v ∨ n.1 v = v) ↔ v = a ∨ v = b) := by
  classical
  let C := (overlay m n).connectedComponentMk a
  have hm : ∀ v, m.1 v ∈ C.supp ↔ v ∈ C.supp := by
    intro v
    change m.1 v ∈ ((overlay m n).connectedComponentMk a).supp ↔
      v ∈ ((overlay m n).connectedComponentMk a).supp
    rw [component_mem_iff, component_mem_iff, reachable_mate_left_iff]
  have hn : ∀ v, n.1 v ∈ C.supp ↔ v ∈ C.supp := by
    intro v
    change n.1 v ∈ ((overlay m n).connectedComponentMk a).supp ↔
      v ∈ ((overlay m n).connectedComponentMk a).supp
    rw [component_mem_iff, component_mem_iff, reachable_mate_right_iff]
  let mC := restrictMate m C.supp hm
  let nC := restrictMate n C.supp hn
  let aC : C.supp := ⟨a, by change (overlay m n).connectedComponentMk a = C; rfl⟩
  have hco : (overlay mC nC).Connected := by
    dsimp only [mC, nC]
    rw [overlay_restrict]
    exact C.connected_toSimpleGraph
  have hdiff : ∀ v : C.supp, mC.1 v ≠ nC.1 v := by
    intro v he
    have hval := congrArg Subtype.val he
    have hav : (overlay m n).Reachable a v.1 := (component_mem_iff m n a v.1).mp v.2
    have han : m.1 a ≠ n.1 a := by rw [hma]; exact Ne.symm hna
    exact mates_ne_of_reachable m n hav han hval
  have hda : (overlay mC nC).degree aC = 1 := by
    rw [overlay_degree_one_iff mC nC aC (hdiff aC)]
    left
    apply Subtype.ext
    exact hma
  obtain ⟨bC, hba, hb⟩ := degree_one_pair (overlay mC nC) hco
    (overlay_degree_le_two mC nC) aC hda
  refine ⟨bC.1, ?_, (component_mem_iff m n a _).mp bC.2, ?_⟩
  · intro he
    exact hba (Subtype.ext he)
  · intro v hv
    let vC : C.supp := ⟨v, (component_mem_iff m n a v).mpr hv⟩
    have hh := hb vC
    rw [overlay_degree_one_iff mC nC vC (hdiff vC)] at hh
    simpa only [mC, nC, vC, aC, Subtype.ext_iff, restrictMate_apply] using hh

noncomputable def weight [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (m : Mate V) : ℝ := ∏ v, if v < m.1 v then w v (m.1 v) else 1

theorem weight_nonneg [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (m : Mate V) : 0 ≤ weight w m := by
  apply Finset.prod_nonneg
  intro v _
  split_ifs
  · exact hw _ _
  · norm_num

theorem switched_weight [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (m n : Mate V) (a : V) :
    weight w (switched m n a) * weight w (switched n m a) = weight w m * weight w n := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : (overlay m n).Reachable a v <;>
    simp [switched_apply, overlay_comm n m, h, mul_comm]

def HasHoles (m : Mate V) (U : Finset V) : Prop := ∀ v, m.1 v = v ↔ v ∈ U

theorem hasHoles_unique (m : Mate V) {U W : Finset V}
    (hU : HasHoles m U) (hW : HasHoles m W) : U = W := by
  ext v
  exact (hU v).symm.trans (hW v)

theorem no_holes_iff (m : Mate V) : HasHoles m ∅ ↔ ∀ v, m.1 v ≠ v := by
  simp [HasHoles]

theorem switched_holes_perfect [Fintype V] [DecidableEq V] (m n : Mate V) (U : Finset V)
    (hm : HasHoles m U) (hn : HasHoles n ∅) (a : V) (ha : a ∈ U) :
    ∃ b ∈ U.erase a,
      HasHoles (switched m n a) (U \ {a, b}) ∧
      HasHoles (switched n m a) {a, b} := by
  classical
  have hnn : ∀ v, n.1 v ≠ v := (no_holes_iff n).mp hn
  obtain ⟨b, hba, hab, he⟩ := active_component_endpoints m n a ((hm a).mpr ha) (hnn a)
  have he' : ∀ v, (overlay m n).Reachable a v → (m.1 v = v ↔ v = a ∨ v = b) := by
    intro v hv
    simpa only [hnn v, or_false] using he v hv
  have hb : b ∈ U := (hm b).mp ((he' b hab).mpr (Or.inr rfl))
  refine ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, ?_, ?_⟩
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hu : v ∈ U ↔ v = a ∨ v = b := (hm v).symm.trans (he' v hv)
      simp [switched_apply, hv, hnn v, hu]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simpa [switched_apply, hv, hva, hvb] using hm v
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · simpa [switched_apply, overlay_comm n m, hv] using he' v hv
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, overlay_comm n m, hv, hnn v, hva, hvb]

noncomputable def matchings [Fintype V] (U : Finset V) : Finset (Mate V) :=
  Finset.univ.filter (fun m => HasHoles m U)

@[simp] theorem mem_matchings [Fintype V] (m : Mate V) (U : Finset V) :
    m ∈ matchings U ↔ HasHoles m U := by simp [matchings]

noncomputable def partition [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (U : Finset V) : ℝ := ∑ m ∈ matchings U, weight w m

theorem partition_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V) : 0 ≤ partition w U :=
  Finset.sum_nonneg (fun _ _ => weight_nonneg w hw _)

theorem hole_partition_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V)
    (a : V) (ha : a ∈ U) :
    partition w U * partition w ∅ ≤
      ∑ b ∈ U.erase a, partition w (U \ {a, b}) * partition w {a, b} := by
  classical
  let S := (matchings U) ×ˢ (matchings (∅ : Finset V))
  let Q := fun b : V => (matchings (U \ {a, b})) ×ˢ (matchings {a, b})
  let f := fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)
  let W := fun p : Mate V × Mate V => weight w p.1 * weight w p.2
  have hi : Function.Injective f := switch_injective a
  have hd : (↑(U.erase a) : Set V).PairwiseDisjoint Q := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpb : HasHoles p.2 {a, b} :=
      (mem_matchings p.2 _).mp (Finset.mem_product.mp hp).2
    have hpc : HasHoles p.2 {a, c} :=
      (mem_matchings p.2 _).mp (Finset.mem_product.mp hq).2
    have hbm : b ∈ ({a, c} : Finset V) := (hpc b).mp ((hpb b).mpr (by simp))
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbm
    exact hbc (hbm.resolve_left hba)
  have himage : S.image f ⊆ (U.erase a).biUnion Q := by
    intro p hp
    obtain ⟨⟨m, n⟩, hmn, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
    obtain ⟨b, hb, hmb, hnb⟩ := switched_holes_perfect m n U
      ((mem_matchings m U).mp hm) ((mem_matchings n ∅).mp hn) a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb,
      Finset.mem_product.mpr ⟨(mem_matchings _ _).mpr hmb, (mem_matchings _ _).mpr hnb⟩⟩
  calc
    partition w U * partition w ∅ = ∑ p ∈ S, W p := by
      simp only [S, W, partition, Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ p ∈ S.image f, W p := by
      rw [Finset.sum_image hi.injOn]
      apply Finset.sum_congr rfl
      intro p _
      exact (switched_weight w p.1 p.2 a).symm
    _ ≤ ∑ p ∈ (U.erase a).biUnion Q, W p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p _ _ => mul_nonneg (weight_nonneg w hw p.1) (weight_nonneg w hw p.2))
    _ = _ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Q, W, partition, Finset.sum_product, Finset.sum_mul_sum]

end MatchingFPRAS.Switching

end OAI
