import OAI.Combinatorics.Hamiltonian.Contraction

namespace OAI

/-! Exact duality under finite network minors. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def fullBlack (black : V → Prop) (U : Finset F) : Finset V :=
  Finset.univ.filter fun v => black v ∧ N.star v ⊆ D.inducedEdges U

def regionBlack (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ((N.fullBlack D black U).filter fun v => v ∈ N.regionShore D U q).card

omit [Fintype F] in
lemma sum_regionBlack (black : V → Prop) (U : Finset F) :
    ∑ q : N.Regions D U, N.regionBlack D black U q = (N.fullBlack D black U).card := by
  simp only [regionBlack,Finset.card_filter,N.mem_regionShore]
  rw [Finset.sum_comm]
  simp

omit [Fintype F] in
lemma regionBalance_singleton (black : V → Prop) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) :
    N.regionBalance D black U q = colorSign black v := by
  simp [regionBalance,hq]

omit [Fintype F] in
lemma regionBalance_complement_singleton (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) {v : V} (hq : (N.regionShore D U q)ᶜ = {v}) :
    N.regionBalance D black U q = -colorSign black v := by
  have hh := Finset.sum_add_sum_compl (N.regionShore D U q) (colorSign black)
  rw [N.colorSign_sum hN h3 black hc,hq,Finset.sum_singleton] at hh
  change (∑ v ∈ N.regionShore D U q, colorSign black v) = _
  omega

omit [Fintype F] in
lemma singleton_regionBlack (hN : N.Simple) (black : V → Prop)
    (U : Finset F) (q : N.Regions D U) {v : V}
    (hq : N.regionShore D U q = {v}) (hv : black v) :
    1 ≤ N.regionBlack D black U q := by
  apply Finset.card_pos.mpr
  refine ⟨v,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · simp only [fullBlack,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hv,N.singleton_region_star D hN U q hq⟩
  · simp [hq]

omit [Fintype F] in

lemma region_density (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U) :
    4 + N.regionBalance D black U q - 2*(N.regionBlack D black U q : ℤ) ≤ N.rim D U q := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  have hd := N.rim_ge_three D hcut U hm q
  by_cases hd4 : 4 ≤ N.rim D U q
  · have hh := rim_defect (N.blackRim D black U q) (N.rim D U q)
      (N.regionBalance D black U q) (N.blackRim_le D black U q) hd4
      (N.region_balance_rim D hN h3 black hc U q)
    omega
  · have hd3 : N.rim D U q = 3 := by omega
    rcases htr _ (N.rim_three_cut D hcut U hm q hd3) with hsing | hsing
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hβ := N.regionBalance_singleton D black U q hv
      by_cases hb : black v
      · have hB := N.singleton_regionBlack D hN black U q hv hb
        simp only [colorSign,hb,ite_true] at hβ
        omega
      · simp only [colorSign,hb,ite_false] at hβ
        omega
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hvr := N.complement_singleton_root D hN h3 hcut U root hr q hd3 hv
      have hβ := N.regionBalance_complement_singleton D hN h3 black hc U q hv
      rw [hvr] at hβ
      simp only [colorSign,hbroot,ite_true] at hβ
      omega

theorem induced_density (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) :
    ((D.inducedEdges U).card : ℤ) - (N.fullBlack D black U).card ≤ 2*(U.card : ℤ)-4 := by
  have hU : U.Nonempty := by
    have hstar : (N.star root).Nonempty := Finset.card_pos.mp (by rw [N.card_star hN,h3 root]; decide)
    obtain ⟨e,he⟩ := hstar
    exact ⟨D.tail e,((D.mem_inducedEdges U e).mp (hr he)).1⟩
  have heuler := N.induced_euler_bound D h U hU
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun q _ => N.region_density D hN h3 hcut htr black hc root hbroot U hr q)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,← Nat.cast_sum,
    N.sum_regionBalance D hN h3 black hc,N.sum_regionBlack,N.sum_rim] at hsum
  push_cast at hsum
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma three_corner_count (p : Fin 3 → Prop) :
    ((min (2 : ℕ) ((Finset.univ.filter fun i => ¬p i).card) : ℕ) : ℤ) +
      (∑ i : Fin 3, if p i ∧ p (i+1) then (1 : ℤ) else 0) =
        2 + if ∀ i, p i then 1 else 0 := by
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;>
    simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.forall_fin_succ] <;>
    norm_num [h0,h1,h2,h11,h21]

omit [Fintype V] [Fintype F] in
lemma Triangle.edges_in_count {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    ((s.filter fun e => e ∈ D.inducedEdges U).card : ℤ) =
      ∑ i : Fin 3, if t.corner i ∈ U ∧ t.corner (i+1) ∈ U then (1 : ℤ) else 0 := by
  conv_lhs => rw [← t.edge_range]
  rw [Finset.filter_image,Finset.card_image_of_injective _ t.edge_injective,
    Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := t.edge_ends i
  have hh : t.edge i ∈ D.inducedEdges U ↔ t.corner i ∈ U ∧ t.corner (i+1) ∈ U := by
    rw [D.mem_inducedEdges]
    rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,and_comm]
  simp [hh]

omit [Fintype V] [Fintype F] in
lemma Triangle.all_corners {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    s ⊆ D.inducedEdges U ↔ ∀ i, t.corner i ∈ U := by
  constructor
  · intro h i
    have hm : t.edge i ∈ s := by
      have hi : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      simpa only [t.edge_range] using hi
    have he := (D.mem_inducedEdges U _).mp (h hm)
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · exact ht ▸ he.1
    · exact hh ▸ he.2
  · intro h e he
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    apply (D.mem_inducedEdges U _).mpr
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,h]

omit [Fintype F] in
lemma black_edge_partition (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (K : Finset E) :
    ∑ v ∈ Finset.univ.filter black, ((N.star v).filter fun e => e ∈ K).card = K.card := by
  have hstar : ∀ v, ((N.star v).filter fun e => e ∈ K) =
      K.filter fun e => N.Incident e v := by
    intro v; ext e; simp [star,and_comm]
  simp only [hstar,Finset.card_filter]
  rw [Finset.sum_comm]
  have he (e : E) : ∀ v, black v → (N.Incident e v ↔ N.blackEndpoint black e = v) := by
    intro v hv
    exact ⟨N.blackEndpoint_eq black hc hv,fun hh => hh ▸ (N.blackEndpoint_spec black hc e).2⟩
  conv_rhs => rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro e _
  have hrewrite : ∀ v ∈ Finset.univ.filter black,
      (if N.Incident e v then 1 else 0 : ℕ) = if N.blackEndpoint black e = v then 1 else 0 := by
    intro v hv; rw [he e v ((Finset.mem_filter.mp hv).2)]
  rw [Finset.sum_congr rfl hrewrite]
  simp [(N.blackEndpoint_spec black hc e).1]

lemma black_dual_card (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    Fintype.card F = (Finset.univ.filter black).card + 2 := by
  have hdeg : ∀ v, N.graph.degree v = 3 := h3
  have he := N.black_edge_partition black hc Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star hN,hdeg,
    Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hv := N.cubic_region_count hN h3 Finset.univ
  have hcut : N.cut Finset.univ = ∅ := by ext e; simp [cut]
  have hreg : N.regionEdges Finset.univ = Finset.univ := by ext e; simp [regionEdges]
  rw [hcut,hreg,Finset.card_empty,Finset.card_univ] at hv
  simp only [Finset.card_univ,add_zero] at hv
  have heu := h.euler N D
  omega

omit [Fintype F] in
lemma capacity_identity (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (U : Finset F) :
    (∑ v ∈ Finset.univ.filter black,
      ((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ)) +
        (D.inducedEdges U).card =
      2 * ((Finset.univ.filter black).card : ℤ) + (N.fullBlack D black U).card := by
  have he := N.black_edge_partition black hc (D.inducedEdges U)
  have hb : (∑ v ∈ Finset.univ.filter black,
      if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) = (N.fullBlack D black U).card := by
    simp only [fullBlack,Finset.card_filter,Nat.cast_sum,Finset.sum_filter,
      ite_and,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  calc
    _ = ∑ v ∈ Finset.univ.filter black,
        (((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ) +
        ((N.star v).filter fun e => e ∈ D.inducedEdges U).card) := by
      simp only [Finset.sum_add_distrib,← Nat.cast_sum,he]
    _ = ∑ v ∈ Finset.univ.filter black,
        (2 + if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [(face v).edges_in_count D U]
      simp only [(face v).all_corners D U]
      convert three_corner_count (fun i => (face v).corner i ∈ U) using 1 <;> congr!
    _ = _ := by rw [Finset.sum_add_distrib,hb]; simp [mul_comm]

theorem capacity_full (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (S : Finset F)
    (hr : ∀ i, (face root).corner i ∉ S) :
    2*S.card ≤ ∑ v ∈ Finset.univ.filter black,
      min 2 ((Finset.univ.filter fun i => (face v).corner i ∈ S).card) := by
  have hd := N.induced_density D h hN h3 hcut htr black hc root hbroot Sᶜ
    ((face root).all_corners D Sᶜ |>.mpr (by simpa using hr))
  have hi := N.capacity_identity D face black hc Sᶜ
  simp only [Finset.mem_compl,not_not] at hi
  have hu := Finset.card_add_card_compl S
  have hb := N.black_dual_card D h hN h3 black hc
  simp only [← Nat.cast_sum] at hi
  omega

end
end Barnette.Network

end OAI
