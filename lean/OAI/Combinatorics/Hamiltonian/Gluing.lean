import OAI.Combinatorics.Hamiltonian.CappedDuality

namespace OAI

/-! Compatible boundary matchings and strong induction over three-edge cuts. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capMatchingEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma restrict_star_image (S : Finset E) (v : V) :
    ((N.restrict (Subtype.val : S → E)).star v).image Subtype.val =
      (N.star v).filter (· ∈ S) := by
  ext e
  simp only [Finset.mem_image,Finset.mem_filter,mem_star]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨hk,k.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

lemma matching_complement_two (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (P : Finset E) (hP : ∀ v, ((N.star v).filter (· ∈ P)).card = 1) :
    (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.IsRegularOfDegree 2 := by
  intro v
  rw [← card_star _ (hN.restrict N _ Subtype.val_injective),
    ← Finset.card_image_of_injective _ Subtype.val_injective,N.restrict_star_image]
  have he := Finset.card_filter_add_card_filter_not (s := N.star v) (p := fun e => e ∈ P)
  rw [hP v,N.card_star hN,hc v] at he
  simpa only [Finset.mem_compl] using (show ((N.star v).filter (fun e => e ∉ P)).card = 2 by omega)

omit [Fintype V] in
lemma cap_matching_some (A : Finset V) (P : Finset (N.regionEdges A)) (v : A) :
    (((N.cap A).star (some v)).filter (· ∈ P)).image Subtype.val =
      (N.star v.val).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_some,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_none (A : Finset V) (P : Finset (N.regionEdges A)) :
    (((N.cap A).star none).filter (· ∈ P)).image Subtype.val =
      (N.cut A).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_none,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_boundary (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1) :
    ∃ c : E, c ∈ N.cut A ∧ c ∈ P.image Subtype.val ∧
      ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  have hh := hP none
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_matching_none] at hh
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hh
  have hmem : c ∈ (N.cut A).filter (· ∈ P.image Subtype.val) := by rw [hc]; simp
  refine ⟨c,(Finset.mem_filter.mp hmem).1,(Finset.mem_filter.mp hmem).2,?_⟩
  intro e he
  have heq : e ∈ (N.cut A).filter (· ∈ P.image Subtype.val) ↔ e = c := by rw [hc]; simp
  simpa only [Finset.mem_filter,he,true_and] using heq

omit [Fintype V] in
lemma cap_image_subset (A : Finset V) (P : Finset (N.regionEdges A)) :
    P.image Subtype.val ⊆ N.regionEdges A := by
  rintro e he
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he
  exact k.property

lemma region_pair_inter (A : Finset V) (e : E) :
    e ∈ N.regionEdges A → e ∈ N.regionEdges Aᶜ → e ∈ N.cut A := by
  simp only [mem_regionEdges,mem_cut,Finset.mem_compl]
  tauto

lemma cap_glue_agrees (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges A) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ P.image Subtype.val := by
  rw [Finset.mem_union,or_iff_left_iff_imp]
  intro hq
  exact (hcut e (N.region_pair_inter A e he (N.cap_image_subset Aᶜ Q hq))).mpr hq

lemma cap_glue_agrees_right (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges Aᶜ) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ Q.image Subtype.val := by
  rw [Finset.mem_union,or_iff_right_iff_imp]
  intro hp
  exact (hcut e (N.region_pair_inter A e (N.cap_image_subset A P hp) he)).mp hp

lemma cap_glue_matching (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    ∀ v, ((N.star v).filter (· ∈ P.image Subtype.val ∪ Q.image Subtype.val)).card = 1 := by
  have side (B : Finset V) (P : Finset (N.regionEdges B)) (R : Finset E)
      (hP : ∀ v, (((N.cap B).star v).filter (· ∈ P)).card = 1)
      (hR : ∀ e ∈ N.regionEdges B, e ∈ R ↔ e ∈ P.image Subtype.val)
      (v : B) : ((N.star v.val).filter (· ∈ R)).card = 1 := by
    have heq : (N.star v.val).filter (· ∈ R) = (N.star v.val).filter (· ∈ P.image Subtype.val) := by
      apply Finset.filter_congr
      intro e he
      apply hR e
      rcases (N.mem_star e v.val).mp he with ht|hh
      · exact (N.mem_regionEdges B e).mpr (Or.inl (ht ▸ v.property))
      · exact (N.mem_regionEdges B e).mpr (Or.inr (hh ▸ v.property))
    rw [heq,← N.cap_matching_some B P v,Finset.card_image_of_injective _ Subtype.val_injective]
    exact hP (some v)
  intro v
  by_cases hv : v ∈ A
  · exact side A P _ hP (N.cap_glue_agrees A P Q hcut) ⟨v,hv⟩
  · exact side Aᶜ Q _ hQ (N.cap_glue_agrees_right A P Q hcut) ⟨v,Finset.mem_compl.mpr hv⟩
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capReachableEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma cap_complement_reachable (A : Finset V) (P : Finset (N.regionEdges A))
    (R : Finset E)
    (hc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hd : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.IsRegularOfDegree 2)
    (hR : ∀ e ∈ N.regionEdges A, e ∈ R ↔ e ∈ P.image Subtype.val)
    (v w : A) : (N.restrict (Subtype.val : ↥Rᶜ → E)).graph.Reachable v.val w.val := by
  let C := ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph
  have hC : (C.induce {x | x ≠ none}).Connected :=
    Barnette.SimpleCycle.delete_vertex_connected C hc hd none
  let f : (C.induce {x | x ≠ none}) →g (N.restrict (Subtype.val : ↥Rᶜ → E)).graph := {
    toFun := fun x => (x.val.getD v).val
    map_rel' := by
      rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
      cases x with
      | none => exact (hx rfl).elim
      | some x =>
        cases y with
        | none => exact (hy rfl).elim
        | some y =>
          obtain ⟨hne,k,hk⟩ := hxy
          have hxy' : x.val ≠ y.val := by
            intro hh
            have hh' : x = y := Subtype.ext hh
            subst y
            exact hne rfl
          have hk' : (N.tail k.val.val = x.val ∧ N.head k.val.val = y.val) ∨
              (N.tail k.val.val = y.val ∧ N.head k.val.val = x.val) := by
            change (N.capMap A (N.tail k.val.val) = some x ∧ N.capMap A (N.head k.val.val) = some y) ∨
              (N.capMap A (N.tail k.val.val) = some y ∧ N.capMap A (N.head k.val.val) = some x) at hk
            simpa only [capMap_eq_some] using hk
          have hnot : k.val.val ∉ P.image Subtype.val := by
            intro hm
            obtain ⟨e,he,hee⟩ := Finset.mem_image.mp hm
            have hee' : e = k.val := Subtype.ext hee
            exact (Finset.mem_compl.mp k.property) (hee' ▸ he)
          have hkR : k.val.val ∈ Rᶜ :=
            Finset.mem_compl.mpr (hnot ∘ (hR k.val.val k.val.property).mp)
          exact ⟨hxy',⟨k.val.val,hkR⟩,hk'⟩ }
  exact (hC ⟨some v,by simp⟩ ⟨some w,by simp⟩).map f

lemma cap_glue_connected (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (h3 : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3)
    (ha : 2 ≤ A.card) (ho : 2 ≤ Aᶜ.card)
    (P : Finset (N.regionEdges A)) (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hPc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hQc : ((N.cap Aᶜ).restrict (Subtype.val : ↥Qᶜ → N.regionEdges Aᶜ)).graph.Connected)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    (N.restrict (Subtype.val : ↥(P.image Subtype.val ∪ Q.image Subtype.val)ᶜ → E)).graph.Connected := by
  have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
  have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
  have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
  have hmP := (N.cap A).matching_complement_two (N.cap_simple hN hc h3 A hA ha ho')
    (N.cap_cubic hN hc h3 A hA ha ho') P hP
  have hmQ := (N.cap Aᶜ).matching_complement_two (N.cap_simple hN hc h3 Aᶜ hc' ho ha'')
    (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'') Q hQ
  let R := P.image Subtype.val ∪ Q.image Subtype.val
  let H := (N.restrict (Subtype.val : ↥Rᶜ → E)).graph
  have rA (v w : A) : H.Reachable v.val w.val :=
    N.cap_complement_reachable A P R hPc hmP (N.cap_glue_agrees A P Q hcut) v w
  have rB (v w : ↥(Aᶜ)) : H.Reachable v.val w.val :=
    N.cap_complement_reachable Aᶜ Q R hQc hmQ (N.cap_glue_agrees_right A P Q hcut) v w
  obtain ⟨c,hcA,hcP,hcuniq⟩ := N.cap_matching_boundary A P hP
  have hdex : ((N.cut A).erase c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hcA,hA]
    decide
  obtain ⟨d,hd⟩ := hdex
  obtain ⟨hdc,hdA⟩ := Finset.mem_erase.mp hd
  have hdP : d ∉ P.image Subtype.val := fun hh => hdc ((hcuniq d hdA).mp hh)
  have hdr : d ∈ N.regionEdges A := by
    have hh := (N.mem_cut A d).mp hdA
    exact (N.mem_regionEdges A d).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
  have hdR : d ∈ Rᶜ := Finset.mem_compl.mpr
    (hdP ∘ (N.cap_glue_agrees A P Q hcut d hdr).mp)
  have adj : H.Adj (N.tail d) (N.head d) := ⟨hN.loopless d,⟨d,hdR⟩,Or.inl ⟨rfl,rfl⟩⟩
  have cross (x y : V) (hx : x ∈ A) (hy : y ∉ A) (hxy : H.Adj x y) : H.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨x,?_⟩
    intro z
    by_cases hz : z ∈ A
    · exact rA ⟨x,hx⟩ ⟨z,hz⟩
    · exact hxy.reachable.trans (rB ⟨y,Finset.mem_compl.mpr hy⟩ ⟨z,Finset.mem_compl.mpr hz⟩)
  rcases (N.mem_cut A d).mp hdA with ⟨ht,hh⟩|⟨hh,ht⟩
  · exact cross _ _ ht hh adj
  · exact cross _ _ hh ht adj.symm
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uV uE uF
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) unrestrictedInductionEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma cap_matching_boundary_at (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (c : E) (hc : c ∈ N.cut A) (hm : c ∈ P.image Subtype.val) :
    ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  obtain ⟨d,_,_,hd⟩ := N.cap_matching_boundary A P hP
  have hh : c = d := (hd c hc).mp hm
  subst d
  exact hd

lemma nontrivial_threeCut_at (h : ¬N.TrivialThreeCuts) (e : E) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card ∧ e ∈ N.regionEdges A := by
  obtain ⟨A,hA,ha,ho⟩ := N.nontrivial_threeCut h
  by_cases he : e ∈ N.regionEdges A
  · exact ⟨A,hA,ha,ho,he⟩
  · have ht : N.tail e ∉ A := fun hh => he ((N.mem_regionEdges A e).mpr (Or.inl hh))
    refine ⟨Aᶜ,by simpa only [cut_compl] using hA,ho,by simpa only [compl_compl] using ha,?_⟩
    exact (N.mem_regionEdges Aᶜ e).mpr (Or.inl (Finset.mem_compl.mpr ht))

private theorem matching_strong (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
      (N : Network V E) (D : Network F E), Fintype.card V = n →
      N.Duality D → N.Simple → N.graph.IsRegularOfDegree 3 → N.ThreeEdgeConnected →
      ∀ (black : V → Prop), (∀ e, black (N.tail e) ↔ ¬black (N.head e)) →
      ∀ e : E, ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
        (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E F _ _ _ N D hn h hN hc h3 black hb e
    by_cases ht : N.TrivialThreeCuts
    · obtain ⟨M⟩ := N.make_coloredDual D h hN h3 hc black hb
      exact N.irreducible_matching D M h3 ht e
    · obtain ⟨A,hA,ha,ho,he⟩ := N.nontrivial_threeCut_at ht e
      have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
      have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
      have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
      have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
      obtain ⟨F₁,f₁,D₁,h₁⟩ := N.cap_duality D h hN h3 A hA ha' ho'
      let : Fintype F₁ := f₁
      have hlt₁ : Fintype.card (Option A) < n := hn ▸ cap_card_lt A ho
      obtain ⟨P,heP,hP,hPc⟩ := ih _ hlt₁ (N.cap A) D₁ rfl h₁
        (N.cap_simple hN hc h3 A hA ha ho') (N.cap_cubic hN hc h3 A hA ha ho')
        (N.cap_threeConnected h3 A ho') (N.capBlack black A)
        (N.cap_coloring hN hc black hb A hA) ⟨e,he⟩
      obtain ⟨c,hca,hcp,hcu⟩ := N.cap_matching_boundary A P hP
      have hcb : c ∈ N.cut Aᶜ := by simpa only [cut_compl] using hca
      have hcr : c ∈ N.regionEdges Aᶜ := by
        have hh := (N.mem_cut Aᶜ c).mp hcb
        exact (N.mem_regionEdges Aᶜ c).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
      obtain ⟨F₂,f₂,D₂,h₂⟩ := N.cap_duality D h hN h3 Aᶜ hc' ho' ha''
      let : Fintype F₂ := f₂
      have hlt₂ : Fintype.card (Option ↥(Aᶜ)) < n := by
        rw [← hn]
        exact cap_card_lt Aᶜ (by simpa only [compl_compl] using ha)
      obtain ⟨Q,hcQ,hQ,hQc⟩ := ih _ hlt₂ (N.cap Aᶜ) D₂ rfl h₂
        (N.cap_simple hN hc h3 Aᶜ hc' ho ha'') (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'')
        (N.cap_threeConnected h3 Aᶜ ha'') (N.capBlack black Aᶜ)
        (N.cap_coloring hN hc black hb Aᶜ hc') ⟨c,hcr⟩
      have hcQ' : c ∈ Q.image Subtype.val := Finset.mem_image.mpr ⟨⟨c,hcr⟩,hcQ,rfl⟩
      have hqcut : ∀ d ∈ N.cut A, d ∈ Q.image Subtype.val ↔ d = c := by
        simpa only [cut_compl] using N.cap_matching_boundary_at Aᶜ Q hQ c hcb hcQ'
      have hcut : ∀ d ∈ N.cut A, d ∈ P.image Subtype.val ↔ d ∈ Q.image Subtype.val :=
        fun d hd => (hcu d hd).trans (hqcut d hd).symm
      refine ⟨P.image Subtype.val ∪ Q.image Subtype.val,?_,N.cap_glue_matching A P Q hP hQ hcut,?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨e,he⟩,heP,rfl⟩)
      · exact N.cap_glue_connected hN hc h3 A hA ha ho P Q hP hQ hPc hQc hcut

variable {F : Type uF} [Fintype F] (D : Network F E)

theorem Duality.connected_complement_matching (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
      (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected :=
  matching_strong (Fintype.card V) N D rfl h hN hc h3 black hb e
end
end Barnette.Network

end OAI
