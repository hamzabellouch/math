import OAI.Combinatorics.Hamiltonian.MinorDuality

namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

lemma count_sum {C D : Type*} [Fintype C] [Fintype D] (p : C ⊕ D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun c => p (.inl c)).card +
      (Finset.univ.filter fun d => p (.inr d)).card := by
  simp only [Finset.card_filter,Fintype.sum_sum_type]

lemma count_prod {C D : Type*} [Fintype C] [Fintype D] (p : C × D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ c, (Finset.univ.filter fun d => p (c,d)).card := by
  simp only [Finset.card_filter,Fintype.sum_prod_type]

abbrev Inc (R : A → B → Prop) := {z : A × B // R z.1 z.2}
abbrev Left (R : A → B → Prop) := (A × Fin 2) ⊕ Inc R
abbrev Right (R : A → B → Prop) := (B × Fin 2) ⊕ Inc R

def gadget (R : A → B → Prop) : Left R → Right R → Prop
  | .inl (a,_), .inr e => e.val.1 = a
  | .inr e, .inl (b,_) => e.val.2 = b
  | .inr e, .inr f => e = f
  | _, _ => False

lemma incidence_fiber (R : A → B → Prop) (S : Finset A) (b : B) :
    ((Finset.univ.filter fun e : Inc R => e.val.1 ∈ S).filter
      fun e => e.val.2 = b).card = (S.filter fun a => R a b).card := by
  apply Finset.card_bij (fun e _ => e.val.1)
  · intro e he
    obtain ⟨he,hb⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).2,hb ▸ e.property⟩
  · intro e he f hf hh
    apply Subtype.ext
    exact Prod.ext hh ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  · intro a ha
    obtain ⟨ha,hab⟩ := Finset.mem_filter.mp ha
    exact ⟨⟨(a,b),hab⟩,by simp [ha],rfl⟩

lemma gadget_hall (R : A → B → Prop)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card))
    (L : Finset (Left R)) :
    L.card ≤ (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card := by
  let S := Finset.univ.filter fun a : A => ∃ k : Fin 2, Sum.inl (a,k) ∈ L
  let T := Finset.univ.filter fun e : Inc R => Sum.inr e ∈ L
  let I := Finset.univ.filter fun e : Inc R => e.val.1 ∈ S
  let Y := Finset.univ.filter fun b : B => ∃ e ∈ T, e.val.2 = b
  have hLc : L.card ≤ 2*S.card + T.card := by
    have hL : L = Finset.univ.filter (fun l => l ∈ L) := by ext; simp
    conv_lhs => rw [hL,count_sum (fun l : Left R => l ∈ L),count_prod]
    change (∑ a, (Finset.univ.filter fun k : Fin 2 => Sum.inl (a,k) ∈ L).card) +
      T.card ≤ _
    apply Nat.add_le_add_right
    calc
      _ ≤ ∑ a, if a ∈ S then 2 else 0 := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a ∈ S
        · simp only [ha,ite_true]
          exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
        · have hn : ∀ k : Fin 2, Sum.inl (a,k) ∉ L := by simpa [S] using ha
          simp [ha,hn]
      _ = 2*S.card := by simp [mul_comm]
  have hY (b : B) (k : Fin 2) :
      (∃ l ∈ L, gadget R l (.inl (b,k))) ↔ b ∈ Y := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a => exact hg.elim
      | inr e => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,by simp [T,hl],hg⟩
    · intro hb
      obtain ⟨e,he,hb⟩ := (Finset.mem_filter.mp hb).2
      exact ⟨.inr e,(Finset.mem_filter.mp he).2,hb⟩
  have hI (e : Inc R) : (∃ l ∈ L, gadget R l (.inr e)) ↔ e ∈ I ∪ T := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a =>
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.2,?_⟩⟩
        change e.val.1 = a.1 at hg
        simpa only [hg] using hl
      | inr f =>
        change f = e at hg
        exact Finset.mem_union_right _ (by simpa [T,← hg] using hl)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨k,hk⟩ := (Finset.mem_filter.mp ((Finset.mem_filter.mp he).2)).2
        exact ⟨.inl (e.val.1,k),hk,rfl⟩
      · exact ⟨.inr e,(Finset.mem_filter.mp he).2,rfl⟩
  have hNc : (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card =
      2*Y.card + (I ∪ T).card := by
    rw [count_sum (fun r : Right R => ∃ l ∈ L, gadget R l r),count_prod]
    simp only [hY,hI]
    have hconst (b : B) : (Finset.univ.filter fun _ : Fin 2 => b ∈ Y).card =
        if b ∈ Y then 2 else 0 := by by_cases hb : b ∈ Y <;> simp [hb]
    have hfilter : (Finset.univ.filter fun e : Inc R => e ∈ I ∪ T) = I ∪ T := by ext; simp
    rw [hfilter]
    simp only [hconst]
    simp [mul_comm]
  have hcap' : 2*S.card ≤ 2*Y.card + (I \ T).card := by
    have hsum : ∑ b, min 2 ((S.filter fun a => R a b).card) ≤
        (∑ b, if b ∈ Y then 2 else 0) + ∑ b, ((I \ T).filter fun e => e.val.2 = b).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b ∈ Y
      · simp only [hb,ite_true]
        exact le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)
      · have hIT : (I \ T).filter (fun e => e.val.2 = b) = I.filter (fun e => e.val.2 = b) := by
          ext e
          simp only [Finset.mem_filter,Finset.mem_sdiff]
          constructor
          · exact fun ⟨⟨hi,_⟩,he⟩ => ⟨hi,he⟩
          · rintro ⟨hi,he⟩
            refine ⟨⟨hi,fun ht => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,ht,he⟩)⟩,he⟩
        rw [hIT]
        dsimp only [I]
        rw [incidence_fiber]
        simp only [hb,ite_false,zero_add]
        exact Nat.min_le_right _ _
    have hcount : ∑ b, ((I \ T).filter fun e => e.val.2 = b).card = (I \ T).card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter (I \ T) Finset.univ (fun e => e.val.2)
    rw [hcount] at hsum
    have hycount : (∑ b, if b ∈ Y then 2 else 0 : ℕ) = 2*Y.card := by
      simp [mul_comm]
    rw [hycount] at hsum
    exact (hcap S).trans hsum
  rw [hNc,← Finset.card_sdiff_add_card]
  omega

theorem gadget_matching (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f : Left R ≃ Right R, ∀ l, gadget R l (f l) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective (gadget R)).mp
    (gadget_hall R hcap)
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,hcard]⟩
  exact ⟨Equiv.ofBijective f hb,hf⟩

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

structure FactorData (R : A → B → Prop) where
  left : A × Fin 2 ↪ Inc R
  right : B × Fin 2 ↪ Inc R
  left_coord : ∀ a k, (left (a,k)).val.1 = a
  right_coord : ∀ b k, (right (b,k)).val.2 = b
  same_range : Set.range left = Set.range right

omit [Fintype A] [Fintype B] in
lemma data_of_gadget (R : A → B → Prop) (f : Left R ≃ Right R)
    (hf : ∀ l, gadget R l (f l)) : Nonempty (FactorData R) := by
  have hleft : ∀ ak : A × Fin 2, ∃ e : Inc R, f (.inl ak) = .inr e ∧ e.val.1 = ak.1 := by
    intro ak
    have h := hf (.inl ak)
    cases he : f (.inl ak) with
    | inl bk => rw [he] at h; exact h.elim
    | inr e => rw [he] at h; exact ⟨e,rfl,h⟩
  have hright : ∀ bk : B × Fin 2, ∃ e : Inc R, f (.inr e) = .inl bk ∧ e.val.2 = bk.1 := by
    intro bk
    obtain ⟨l,hl⟩ := f.surjective (.inl bk)
    have h := hf l
    rw [hl] at h
    cases l with
    | inl ak => exact h.elim
    | inr e => exact ⟨e,hl,h⟩
  choose l hl hlc using hleft
  choose r hr hrc using hright
  have hli : Function.Injective l := by
    intro a b h
    exact Sum.inl.inj (f.injective ((hl a).trans ((congrArg Sum.inr h).trans (hl b).symm)))
  have hri : Function.Injective r := by
    intro a b h
    exact Sum.inl.inj ((hr a).symm.trans ((congrArg (fun e => f (.inr e)) h).trans (hr b)))
  refine ⟨⟨⟨l,hli⟩,⟨r,hri⟩,fun a k => hlc (a,k),fun b k => hrc (b,k),?_⟩⟩
  ext e
  constructor
  · rintro ⟨ak,rfl⟩
    have h := hf (.inr (l ak))
    cases he : f (.inr (l ak)) with
    | inl bk =>
      exact ⟨bk,Sum.inr.inj (f.injective ((hr bk).trans he.symm))⟩
    | inr d =>
      rw [he] at h
      change l ak = d at h
      have hh : Sum.inl ak = Sum.inr (l ak) := f.injective ((hl ak).trans (by simpa [h] using he.symm))
      cases hh
  · rintro ⟨bk,rfl⟩
    obtain ⟨z,hz⟩ := f.surjective (.inr (r bk))
    have h := hf z
    rw [hz] at h
    cases z with
    | inl ak => exact ⟨ak,Sum.inr.inj ((hl ak).symm.trans hz)⟩
    | inr e =>
      change e = r bk at h
      subst e
      have hh := (hr bk).symm.trans hz
      cases hh

lemma two_image_count {C : Type*} [Fintype C] (f : Fin 2 → C) (hf : Function.Injective f) :
    (Finset.univ.filter fun c => ∃ k, f k = c).card = 2 := by
  have hs : (Finset.univ.filter fun c => ∃ k, f k = c) = Finset.univ.image f := by ext; simp
  rw [hs,Finset.card_image_of_injective _ hf]
  simp

lemma data_two_factor (R : A → B → Prop) (M : FactorData R) :
    ∃ Q : A → B → Prop, (∀ a b, Q a b → R a b) ∧
      (∀ a, (Finset.univ.filter (Q a)).card = 2) ∧
      (∀ b, (Finset.univ.filter fun a => Q a b).card = 2) := by
  classical
  let Q : A → B → Prop := fun a b => ∃ k, (M.left (a,k)).val.2 = b
  have hQright (a : A) (b : B) : Q a b ↔ ∃ k, (M.right (b,k)).val.1 = a := by
    constructor
    · rintro ⟨k,hk⟩
      have he : M.left (a,k) ∈ Set.range M.right := M.same_range ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = b := (M.right_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.2) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.1) he).trans (M.left_coord a k)⟩
    · rintro ⟨k,hk⟩
      have he : M.right (b,k) ∈ Set.range M.left := M.same_range.symm ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = a := (M.left_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.1) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.2) he).trans (M.right_coord b k)⟩
  refine ⟨Q,?_,?_,?_⟩
  · rintro a b ⟨k,rfl⟩
    have h := (M.left (a,k)).property
    rwa [M.left_coord] at h
  · intro a
    have hi : Function.Injective (fun k => (M.left (a,k)).val.2) := by
      intro i j hij
      have he : M.left (a,i) = M.left (a,j) := Subtype.ext (Prod.ext (by simp [M.left_coord]) hij)
      exact Prod.mk.inj (M.left.injective he) |>.2
    simpa only [Q] using two_image_count (fun k => (M.left (a,k)).val.2) hi
  · intro b
    simp only [hQright]
    apply two_image_count
    intro i j hij
    have he : M.right (b,i) = M.right (b,j) := Subtype.ext (Prod.ext hij (by simp [M.right_coord]))
    exact Prod.mk.inj (M.right.injective he) |>.2

lemma regular_hall (Q : A → B → Prop) (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n)
    (S : Finset A) :
    S.card ≤ (Finset.univ.filter fun b => ∃ a ∈ S, Q a b).card := by
  let T := Finset.univ.filter fun b => ∃ a ∈ S, Q a b
  have hc : n*S.card = ∑ b, (S.filter fun a => Q a b).card := by
    calc
      _ = ∑ a ∈ S, (Finset.univ.filter (Q a)).card := by simp [hrow,mul_comm]
      _ = _ := by simp only [Finset.card_filter]; rw [Finset.sum_comm]
  have hl : ∑ b, (S.filter fun a => Q a b).card ≤ ∑ b, if b ∈ T then n else 0 := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ T
    · simp only [hb,ite_true]
      rw [← hcol b]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    · have hnone : ∀ a ∈ S, ¬Q a b := by simpa [T] using hb
      simp [hb,Finset.filter_false_of_mem hnone]
  have hr : (∑ b, if b ∈ T then n else 0) = n*T.card := by simp [mul_comm]
  rw [hr,← hc] at hl
  exact Nat.le_of_mul_le_mul_left hl hn

lemma regular_matching (Q : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n) :
    ∃ f : A ≃ B, ∀ a, Q a (f a) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective Q).mp
    (regular_hall Q n hn hrow hcol)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hcard⟩),hf⟩

theorem two_matchings (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f g : A ≃ B, (∀ a, R a (f a) ∧ R a (g a)) ∧ (∀ a, f a ≠ g a) := by
  classical
  obtain ⟨p,hp⟩ := gadget_matching R hcard hcap
  obtain ⟨M⟩ := data_of_gadget R p hp
  obtain ⟨Q,hQR,hrow,hcol⟩ := data_two_factor R M
  obtain ⟨f,hf⟩ := regular_matching Q hcard 2 (by decide) hrow hcol
  let Q' : A → B → Prop := fun a b => Q a b ∧ b ≠ f a
  have hr : ∀ a, (Finset.univ.filter (Q' a)).card = 1 := by
    intro a
    have he : Finset.univ.filter (Q' a) = (Finset.univ.filter (Q a)).erase (f a) := by
      ext b; simp [Q',and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hf a]),hrow]
  have hc : ∀ b, (Finset.univ.filter fun a => Q' a b).card = 1 := by
    intro b
    have he : (Finset.univ.filter fun a => Q' a b) =
        (Finset.univ.filter fun a => Q a b).erase (f.symm b) := by
      ext a
      simp only [Q',Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
      constructor
      · rintro ⟨hq,hne⟩
        exact ⟨fun he => hne (by rw [he,f.apply_symm_apply]),hq⟩
      · rintro ⟨hne,hq⟩
        exact ⟨hq,fun he => hne (f.injective (by simpa using he.symm))⟩
    rw [he,Finset.card_erase_of_mem (by simpa using hf (f.symm b)),hcol]
  obtain ⟨g,hg⟩ := regular_matching Q' hcard 1 (by decide) (by simpa only [Q'] using hr) (by simpa only [Q'] using hc)
  exact ⟨f,g,fun a => ⟨hQR _ _ (hf a),hQR _ _ (hg a).1⟩,fun a h => (hg a).2 h.symm⟩

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
lemma exists_value (r : A ≃ X) (hr : ∀ t, (r t : V) ∈ Set.range (T.vertex t)) :
    ∃ s : T.State X, ∀ t, s.value t = (r t : V) := by
  choose c hc using hr
  refine ⟨⟨c,?_,?_⟩,hc⟩
  · intro t u h
    exact r.injective (Subtype.ext (by simpa only [hc] using h))
  · ext v
    constructor
    · rintro ⟨t,rfl⟩
      change T.vertex t (c t) ∈ X
      rw [hc]; exact (r t).property
    · intro hv
      obtain ⟨t,ht⟩ := r.surjective ⟨v,hv⟩
      exact ⟨t,(hc t).trans (congrArg Subtype.val ht)⟩
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

lemma nonroots_card (root : V) (hr : M.black root) :
    Fintype.card (M.nonroots root) = Fintype.card (M.Black root) := by
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have hc : Fintype.card (Set.range (M.face root).corner) = 3 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (M.face root).corner_injective)]
    rfl
  have hn := Fintype.card_compl_set (Set.range (M.face root).corner)
  have hb : Fintype.card (M.Black root) = (Finset.univ.filter M.black).card - 1 := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hr])]
  have hnx : Fintype.card (M.nonroots root) =
      Fintype.card F - Fintype.card (Set.range (M.face root).corner) := by
    convert hn using 1
    congr!
  rw [hnx,hc,hb,hf]
  omega

omit [Fintype F] in
lemma corner_filter_card (root : V) (S : Finset (M.nonroots root)) (t : M.Black root) :
    (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).card := by
  have he : (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).image Subtype.val =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).image
        (M.face t.val).corner := by
    ext z
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_range]
    constructor
    · rintro ⟨x,⟨hx,i,hi⟩,rfl⟩
      exact ⟨i,⟨x,hx,hi.symm⟩,hi⟩
    · rintro ⟨i,⟨x,hx,hxi⟩,hi⟩
      exact ⟨x,⟨hx,i,hxi.symm⟩,hxi.trans hi⟩
  have hh := congrArg Finset.card he
  rwa [Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ (M.face t.val).corner_injective] at hh

lemma state_capacity (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) (S : Finset (M.nonroots root)) :
    2*S.card ≤ ∑ t : M.Black root,
      min 2 ((S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card) := by
  let U := S.image Subtype.val
  have hu : ∀ i, (M.face root).corner i ∉ U := by
    intro i hi
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hi
    exact x.property ⟨i,hx.symm⟩
  have hcap := N.capacity_full D M.duality M.simple M.cubic hcut htr M.face M.black
    M.coloring root hr U hu
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcap
  have hz : min 2 ((Finset.univ.filter fun i => (M.face root).corner i ∈ U).card) = 0 := by
    have hh : (Finset.univ.filter fun i => (M.face root).corner i ∈ U) = ∅ := by
      ext i; simp [hu]
    rw [hh]; simp
  have he : (∑ v ∈ Finset.univ.filter M.black,
        min 2 ((Finset.univ.filter fun i => (M.face v).corner i ∈ U).card)) =
      ∑ t : M.Black root, min 2 ((Finset.univ.filter fun i => (M.face t.val).corner i ∈ U).card) := by
    rw [← Finset.sum_erase_add _ _ (show root ∈ Finset.univ.filter M.black by simp [hr]),hz,add_zero]
    apply Finset.sum_subtype
    intro v; simp [and_comm]
  rw [he] at hcap
  simpa only [M.corner_filter_card root S] using hcap

theorem pair_nonempty (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) : Nonempty ((M.system root).Pair (M.nonroots root)) := by
  obtain ⟨f,g,hfg,hne⟩ := Barnette.BMatching.two_matchings
    (fun (x : M.nonroots root) (t : M.Black root) => x.val ∈ Set.range (M.face t.val).corner)
    (M.nonroots_card root hr) (by
      intro S
      convert M.state_capacity hcut htr root hr S using 1; congr!)
  have hf : ∀ t : M.Black root, (f.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (f.symm t)).1
    rw [f.apply_symm_apply] at h
    exact h
  have hg : ∀ t : M.Black root, (g.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (g.symm t)).2
    rw [g.apply_symm_apply] at h
    exact h
  obtain ⟨r,hrv⟩ := Barnette.TriangleSystem.State.exists_value f.symm hf
  obtain ⟨s,hsv⟩ := Barnette.TriangleSystem.State.exists_value g.symm hg
  refine ⟨⟨(r,s),?_⟩⟩
  intro t he
  rw [hrv,hsv] at he
  have hh : f.symm t = g.symm t := Subtype.ext he
  apply hne (f.symm t)
  rw [f.apply_symm_apply,hh,g.apply_symm_apply]

end
end Barnette.Network.ColoredDual

end OAI
