import OAI.Combinatorics.Hamiltonian.Matching

namespace OAI

/-! From opposite forests to connected spanning matching complements. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma complement_coloring (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∀ e, ¬black (N.tail e) ↔ ¬¬black (N.head e) := fun e => not_congr (hc e)

omit [Fintype V] [Fintype E] in
lemma colored_endpoints (black : V → Prop)
    (_hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    s(N.tail e,N.head e) = s(N.blackEndpoint black e,N.blackEndpoint (fun v => ¬black v) e) := by
  by_cases hb : black (N.tail e)
  · simp [blackEndpoint,hb]
  · simp [blackEndpoint,hb,Sym2.eq_swap]

lemma black_fiber_count (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (T : Finset V) (hT : ∀ v ∈ T, black v) :
    (H.filter fun e => N.blackEndpoint black e ∈ T).card =
      ∑ v ∈ T, ((N.star v).filter fun e => e ∈ H).card := by
  rw [← N.black_edge_partition black hc]
  have hf (v : V) (hv : black v) :
      (N.star v).filter (fun e => e ∈ H.filter (fun e => N.blackEndpoint black e ∈ T)) =
        if v ∈ T then (N.star v).filter (fun e => e ∈ H) else ∅ := by
    ext e
    by_cases ht : v ∈ T
    · simp only [ite_eq_left ht,Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨he,hh⟩
        exact ⟨he,hh,(N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ ht⟩
    · simp only [ite_eq_right ht,Finset.notMem_empty,Finset.mem_filter,iff_false]
      rintro ⟨he,_,hbe⟩
      exact ht ((N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ hbe)
  rw [Finset.sum_congr rfl (fun v hv => congrArg Finset.card (hf v (Finset.mem_filter.mp hv).2))]
  simp only [apply_ite Finset.card,Finset.card_empty,Finset.sum_ite_mem]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨And.right,fun hv => ⟨hT v hv,hv⟩⟩

lemma tree_matching (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (hi : Function.Injective (N.restrict (Subtype.val : H → E)).boundary)
    (root : V) (_hr : black root)
    (hd : ∀ v, black v → ((N.star v).filter (fun e => e ∈ H)).card = if v = root then 1 else 2)
    (hbal : Fintype.card {v // black v} = Fintype.card {v // ¬black v}) :
    ∃ P : Finset E, P ⊆ H ∧ ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1 := by
  let B := {v // black v}
  let W := {v // ¬black v}
  let R : B → W → Prop := fun b w => ∃ e ∈ H,
    N.blackEndpoint black e = b.val ∧ N.blackEndpoint (fun v => ¬black v) e = w.val
  have hhall (S : Finset B) : S.card ≤ (Finset.univ.filter fun w : W => ∃ b ∈ S, R b w).card := by
    let Y := Finset.univ.filter fun w : W => ∃ b ∈ S, R b w
    let T := S.image Subtype.val
    let Z := Y.image Subtype.val
    let J := H.filter fun e => N.blackEndpoint black e ∈ T
    have hTc : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hZc : Z.card = Y.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hT : ∀ v ∈ T, black v := by
      intro v hv; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv; exact b.property
    have hZ : ∀ v ∈ Z, ¬black v := by
      intro v hv; obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv; exact w.property
    have hdis : Disjoint T Z := Finset.disjoint_left.mpr (fun v ht hz => hZ v hz (hT v ht))
    by_cases hS : S.Nonempty
    · have hJc : 2*T.card ≤ J.card + 1 := by
        have he := N.black_fiber_count black hc H T hT
        have hd' : ∀ v ∈ T, ((N.star v).filter fun e => e ∈ H).card = 2 - if v = root then 1 else 0 := by
          intro v hv; rw [hd v (hT v hv)]; split_ifs <;> rfl
        have hn (v : V) : (2 - if v = root then 1 else 0 : ℕ) + (if v = root then 1 else 0) = 2 := by split_ifs <;> rfl
        have hh : J.card + ∑ v ∈ T, (if v = root then 1 else 0 : ℕ) = 2*T.card := by
          rw [he,Finset.sum_congr rfl hd',← Finset.sum_add_distrib]
          simp only [hn,Finset.sum_const,smul_eq_mul,mul_comm]
        have hx : (∑ v ∈ T, (if v = root then 1 else 0 : ℕ)) ≤ 1 := by simp; split_ifs <;> omega
        omega
      let J' : Finset H := Finset.univ.filter fun e => e.val ∈ J
      have hJ' : J'.card = J.card := by
        apply Finset.card_bij (fun e _ => e.val)
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro _ _ _ _ hh; exact Subtype.ext hh
        · intro e he; exact ⟨⟨e,(Finset.mem_filter.mp he).1⟩,by simp [J',he],rfl⟩
      have hn : (T ∪ Z).Nonempty := by obtain ⟨b,hb⟩ := hS; exact ⟨b.val,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)⟩
      have hsupp : ∀ e ∈ J', (N.restrict (Subtype.val : H → E)).tail e ∈ T ∪ Z ∧
          (N.restrict (Subtype.val : H → E)).head e ∈ T ∪ Z := by
        intro e he
        have hJ : e.val ∈ J := (Finset.mem_filter.mp he).2
        have hb : N.blackEndpoint black e.val ∈ T := (Finset.mem_filter.mp hJ).2
        obtain ⟨b,hbS,hbe⟩ := Finset.mem_image.mp hb
        let w : W := ⟨N.blackEndpoint (fun v => ¬black v) e.val,
          (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) e.val).1⟩
        have hw : w ∈ Y := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hbS,e.val,e.property,hbe.symm,rfl⟩
        have hz : N.blackEndpoint (fun v => ¬black v) e.val ∈ Z := Finset.mem_image.mpr ⟨w,hw,rfl⟩
        rcases Sym2.eq_iff.mp (N.colored_endpoints black hc e.val) with hh|hh
        · exact ⟨Finset.mem_union_left _ (hh.1 ▸ hb),Finset.mem_union_right _ (hh.2 ▸ hz)⟩
        · exact ⟨Finset.mem_union_right _ (hh.1 ▸ hz),Finset.mem_union_left _ (hh.2 ▸ hb)⟩
      have hb := (N.restrict (Subtype.val : H → E)).independent_edges_bound hi J' (T ∪ Z) hn hsupp
      rw [hJ',Finset.card_union_of_disjoint hdis,hTc,hZc] at hb
      rw [hTc] at hJc
      change S.card ≤ Y.card
      omega
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hz]
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hhall
  have hfs : Function.Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hbal⟩ |>.2
  choose p hp hb hw using hf
  let P := Finset.univ.image p
  have hpP (b : B) : p b ∈ P := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  have hsub : P ⊆ H := by intro e he; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he; exact hp b
  refine ⟨P,hsub,?_⟩
  intro v
  by_cases hv : black v
  · let b : B := ⟨v,hv⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : b' = b := Subtype.ext ((hb b').symm.trans (N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)))
      rw [hh]
    · rintro rfl
      have hh : N.blackEndpoint black (p b) = v := hb b
      exact ⟨(N.mem_star _ _).mpr (hh ▸ (N.blackEndpoint_spec black hc (p b)).2),hpP b⟩
  · obtain ⟨b,hbv⟩ := hfs ⟨v,hv⟩
    have hwv : N.blackEndpoint (fun v => ¬black v) (p b) = v := (hw b).trans (congrArg Subtype.val hbv)
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : f b' = f b := Subtype.ext ((hw b').symm.trans
        ((N.blackEndpoint_eq (fun v => ¬black v) (N.complement_coloring black hc) hv ((N.mem_star _ _).mp he)).trans ((congrArg Subtype.val hbv).symm)))
      rw [hfi hh]
    · rintro rfl
      exact ⟨(N.mem_star _ _).mpr (hwv ▸ (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) (p b)).2),hpP b⟩
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma sum_substars (hN : N.Simple) (P : Finset E) (A : Finset V) :
    ∑ v ∈ A, ((N.star v).filter fun e => e ∈ P).card =
      ∑ e, if e ∈ P then ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) else 0 := by
  calc
    _ = ∑ v ∈ A, ∑ e, if e ∈ P then ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [star,Finset.filter_filter,Finset.card_filter]
      simp only [Incident]
      apply Finset.sum_congr rfl
      intro e _
      have hne := hN.loopless e
      by_cases hp : e ∈ P <;> by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : e ∈ P <;> simp [hp,Finset.sum_add_distrib]

lemma matching_cut_balance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (A : Finset V) (hcut : N.cut A ⊆ P) :
    (N.cut A).card = 2*(N.blackCut black A).card := by
  have hsum := N.sum_substars hN P A
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hsum
  have htotal : A.card + (N.cut A).card = 2*((N.regionEdges A).filter fun e => e ∈ P).card := by
    rw [hsum]
    simp only [cut,regionEdges,Finset.card_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;> by_cases hp : e ∈ P <;> simp_all
  have hbsum := N.sum_substars hN P (A.filter black)
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hbsum
  have hblack : (A.filter black).card + (N.cut A).card =
      ((N.regionEdges A).filter fun e => e ∈ P).card + (N.blackCut black A).card := by
    rw [hbsum]
    simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    have hc' := hc e
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;>
      by_cases hp : e ∈ P <;> by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [blackEndpoint]
  have hcub := N.cubic_region_count hN h3 A
  have hbcub := N.cubic_black_region_count hN h3 black hc A
  omega
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

lemma black_white_balance : Fintype.card {v // M.black v} = Fintype.card {v // ¬M.black v} := by
  have hc := M.cubic_cards.2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype]
  change (Finset.univ.filter M.black).card = Fintype.card V - (Finset.univ.filter M.black).card
  omega

lemma recovery_matching (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    ∃ S : Finset E, S ⊆ (M.removed P i)ᶜ ∧ ∀ v, ((N.star v).filter fun e => e ∈ S).card = 1 :=
  N.tree_matching M.black M.coloring _ (M.remainder_independent P hr ha i) root hr
    (M.remainder_black_degree P hr i) M.black_white_balance

end
end Barnette.Network.ColoredDual
namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
abbrev reverseCycle : Barnette.CycleCoordinates G where
  n := C.n
  vertex := ⟨fun i => C.vertex (-i),fun _ _ h => neg_injective (C.vertex.injective h)⟩
  adjacent i := by
    have hh := (C.adjacent (-i-1)).symm
    change G.Adj (C.vertex (-i)) (C.vertex (-(i+1)))
    rw [sub_add_cancel,show -i-1 = -(i+1) by abel] at hh
    exact hh
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
variable {V E : Type*} (N : Network V E)
lemma directed_cycle_of_not_acyclic (ht : Function.Injective N.tail) (hn : ¬N.graph.IsAcyclic) :
    ∃ (C : Barnette.CycleCoordinates N.graph) (e : Fin (C.n+3) → E),
      ∀ i, N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1) := by
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hn
  let e : Fin (C.n+3) ↪ E := ⟨N.cycleEdge C,N.cycleEdge_injective C⟩
  have he (i) : (N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1)) ∨
      (N.tail (e i) = C.vertex (i+1) ∧ N.head (e i) = C.vertex i) :=
    Sym2.eq_iff.mp (N.cycleEdge_ends C i)
  rcases C.tail_orientation e N.tail ht (fun i => (he i).elim (Or.inl ∘ And.left) (Or.inr ∘ And.left)) with hf|hb
  · refine ⟨C,e,fun i => ⟨hf i,?_⟩⟩
    rcases he i with h|h
    · exact h.2
    · exact ((C.adjacent i).1 ((hf i).symm.trans h.1)).elim
  · refine ⟨C.reverseCycle,fun i => e (-i-1),fun i => ?_⟩
    have hh : N.head (e (-i-1)) = C.vertex (-i-1) := by
      rcases he (-i-1) with h|h
      · exact ((C.adjacent (-i-1)).1 (h.1.symm.trans (hb (-i-1)))).elim
      · exact h.2
    constructor
    · change N.tail (e (-i-1)) = C.vertex (-i)
      simpa only [sub_add_cancel] using hb (-i-1)
    · change N.head (e (-i-1)) = C.vertex (-(i+1))
      exact hh.trans (congrArg C.vertex (show -i-1 = -(i+1) by abel))
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype E] (N : Network V E)

def matchingEdge (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) : E :=
  (Finset.card_eq_one.mp (hd v)).choose

lemma matchingEdge_spec (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    (N.star v).filter (fun e => e ∈ P) = {N.matchingEdge P hd v} :=
  (Finset.card_eq_one.mp (hd v)).choose_spec

lemma matchingEdge_mem (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    N.matchingEdge P hd v ∈ N.star v ∧ N.matchingEdge P hd v ∈ P := by
  exact Finset.mem_filter.mp (by rw [N.matchingEdge_spec P hd v]; exact Finset.mem_singleton_self _)

lemma matchingEdge_eq (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    {v : V} {e : E} (he : e ∈ N.star v) (hp : e ∈ P) : e = N.matchingEdge P hd v := by
  exact Finset.mem_singleton.mp ((N.matchingEdge_spec P hd v) ▸ Finset.mem_filter.mpr ⟨he,hp⟩)
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev selectNet (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) : Network F (M.Black root) where
  tail t := s.value t
  head t := D.otherEnd (N.matchingEdge P hd t.val) (s.value t)

lemma selectNet_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t)) :
    (M.selectNet s P hd).graph.IsAcyclic := by
  by_contra hn
  obtain ⟨C,t,ht⟩ := (M.selectNet s P hd).directed_cycle_of_not_acyclic s.value_injective hn
  have he (i) : s(D.tail (N.matchingEdge P hd (t i).val),D.head (N.matchingEdge P hd (t i).val)) =
      s(C.vertex i,C.vertex (i+1)) := by
    rw [(D.otherEnd_spec M.dual_simple (hi (t i))).2]
    change s((M.selectNet s P hd).tail (t i),(M.selectNet s P hd).head (t i)) = _
    rw [(ht i).1,(ht i).2]
  let C' : Barnette.CycleCoordinates D.graph := {
    n := C.n
    vertex := C.vertex
    adjacent i := ⟨(C.adjacent i).1,N.matchingEdge P hd (t i).val,Sym2.eq_iff.mp (he i)⟩ }
  have hedge (i) : D.cycleEdge C' i = N.matchingEdge P hd (t i).val := by
    apply M.dual_simple.pair_injective
    dsimp only
    rw [D.cycleEdge_ends]
    exact (he i).symm
  obtain ⟨A,c,_,_,_,_,hcut,hcount,_⟩ := M.cycle_disk s C' t
    (fun i => hedge i ▸ (N.matchingEdge_mem P hd (t i).val).1) (fun i => (ht i).1)
  have hsub : N.cut A ⊆ P := by
    intro e he
    rw [hcut] at he
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C' e).mp he
    rw [hedge]
    exact (N.matchingEdge_mem P hd (t i).val).2
  have hbal := N.matching_cut_balance M.simple M.cubic M.black M.coloring P hd A hsub
  omega

lemma selected_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (_hr : M.black root)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t))
    (i : Fin 3) (he0 : N.matchingEdge P hd root = (M.face root).edge i) :
    (D.restrict (Subtype.val : P → E)).graph.IsAcyclic := by
  let L := M.selectNet s P hd
  let K := L.addSink (fun j => (M.face root).corner (rootStart (i+2) j)) ((M.face root).corner (i+2+2))
  have hK : K.graph.IsAcyclic := by
    apply L.addSink_acyclic (M.selectNet_forest s P hd hi) s.value_injective _
      ((M.face root).corner_injective.comp (rootStart_inj (i+2)))
    · intro t j h
      exact s.value_mem t ⟨rootStart (i+2) j,h.symm⟩
    · rintro ⟨t|j,h⟩
      · exact s.value_mem t ⟨i+2+2,h.symm⟩
      · exact rootStart_ne (i+2) j ((M.face root).corner_injective h)
  apply SimpleGraph.IsAcyclic.anti ?_ hK
  intro v w ⟨hvw,e,he⟩
  let b := N.blackEndpoint M.black e.val
  have hb : M.black b := (N.blackEndpoint_spec M.black M.coloring e.val).1
  have heb : e.val ∈ N.star b := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e.val).2
  have hep : e.val = N.matchingEdge P hd b := N.matchingEdge_eq P hd heb e.property
  have hends : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  by_cases hbr : b = root
  · have hstart : rootStart (i+2) 1 = i := by fin_cases i <;> rfl
    have hend : i+2+2 = i+1 := by fin_cases i <;> rfl
    refine ⟨hvw,Sum.inr 1,?_⟩
    apply Sym2.eq_iff.mp
    change s((M.face root).corner (rootStart (i+2) 1),(M.face root).corner (i+2+2)) = s(v,w)
    rw [hstart,hend,← (M.face root).edge_ends i,← he0,← hbr,← hep]
    exact hends
  · let t : M.Black root := ⟨b,hb,hbr⟩
    refine ⟨hvw,Sum.inl t,?_⟩
    apply Sym2.eq_iff.mp
    change s(s.value t,D.otherEnd (N.matchingEdge P hd b) (s.value t)) = s(v,w)
    rw [← (D.otherEnd_spec M.dual_simple (hi t)).2,← hep]
    exact hends

lemma recover_connected_complement (Q : (M.system root).Pair (M.nonroots root))
    (hr : M.black root) (ha : ((M.system root).oppositeGraph Q.right).IsAcyclic) (i : Fin 3) :
    ∃ P : Finset E, (M.face root).edge i ∈ P ∧
      (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  obtain ⟨P,hsub,hd⟩ := M.recovery_matching Q hr ha i
  have hi (t : M.Black root) : D.Incident (N.matchingEdge P hd t.val) (Q.right.value t) :=
    M.remainder_incident Q hr i t (N.matchingEdge_mem P hd t.val).1
      (hsub (N.matchingEdge_mem P hd t.val).2)
  have he0 : N.matchingEdge P hd root = (M.face root).edge i := by
    have hmem := (N.matchingEdge_mem P hd root)
    have hm := M.removed_at_black Q hr i root hr hmem.1
    have hn := (not_congr hm).mp (Finset.mem_compl.mp (hsub hmem.2))
    simpa using hn
  refine ⟨P,he0 ▸ (N.matchingEdge_mem P hd root).2,hd,?_⟩
  exact M.duality.complement_connected N D M.dual_simple P
    (M.selected_forest Q.right P hd hr hi i he0)
end
end Barnette.Network.ColoredDual

end OAI
