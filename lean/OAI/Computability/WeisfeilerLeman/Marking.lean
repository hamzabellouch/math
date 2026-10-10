import OAI.Computability.WeisfeilerLeman.Gadgets

namespace OAI

universe uP uE uV uW uD uS uState

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

def Attainable (K : ℕ) (t : TypeNode K P E) (a : I.Address) : Set (I.Value K t) :=
  {v | ∃ ha ys, I.Queried K (I.siteRing K t a ha) ys ∧ I.horizontalSum K t a ys = v}

theorem attainable_nonempty (K : ℕ)
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none))
    (t : TypeNode K P E) (a : I.Address) (ha : I.AddressAllowed K t a) :
    (I.Attainable K t a).Nonempty := by
  obtain ⟨ys,hys⟩ := I.queried_exists K h (I.siteRing K t a ha)
  exact ⟨_,ha,ys,hys,rfl⟩

private theorem add_eq_rotate {x y b : F₂} (h : x+y=b) : x = y+b := by
  rw [← h,add_left_comm,CharTwo.add_self_eq_zero,add_zero]

theorem attainable_link (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) :
    I.leftForm K l '' I.Attainable K (linkLeft K I.src l) a =
      (fun z => I.rightForm K l z + I.linkBias K l) ''
        I.Attainable K (linkRight K I.dst l) (I.matchedAddress K l a) := by
  ext v
  constructor
  · rintro ⟨x,⟨hx,ys,hys,rfl⟩,rfl⟩
    obtain ⟨zs,hzs,heq⟩ := I.ring_transfer_left K hr l a ha hys
    exact ⟨_,⟨_,zs,hzs,rfl⟩,(add_eq_rotate heq).symm⟩
  · rintro ⟨x,⟨hx,ys,hys,rfl⟩,rfl⟩
    obtain ⟨zs,hzs,heq⟩ := I.ring_transfer_right K hr l a ha hys
    exact ⟨_,⟨_,zs,hzs,rfl⟩,add_eq_rotate heq⟩

theorem mem_attainable_image (K : ℕ) (t : TypeNode K P E) (a : I.Address)
    (f : I.Value K t → F₂) (v : F₂) :
    v ∈ f '' I.Attainable K t a ↔
      ∃ ha ys, I.Queried K (I.siteRing K t a ha) ys ∧ f (I.horizontalSum K t a ys) = v := by
  constructor
  · rintro ⟨x,⟨ha,ys,hys,rfl⟩,hf⟩
    exact ⟨ha,ys,hys,hf⟩
  · rintro ⟨ha,ys,hys,hf⟩
    exact ⟨_,⟨ha,ys,hys,rfl⟩,hf⟩

theorem matchedAddress_internal (K : ℕ) (l : TypeLink K E) (h : l.2.val ≠ 4*K)
    (a : I.Address) : I.matchedAddress K l a = a := by
  funext i
  simp only [matchedAddress,linkMatch,ite_eq_right h,Equiv.refl_apply]

theorem matchedAddress_last (K : ℕ) (l : TypeLink K E) (h : l.2.val = 4*K)
    (a : I.Address) : I.matchedAddress K l a = I.permuteAddress l.1 a := by
  funext i
  simp only [matchedAddress,linkMatch,ite_eq_left h,permuteAddress]

theorem attainable_first (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) :
    I.affineSrc e '' I.Attainable K (.inl (I.src e)) a =
      I.Attainable K (.inr (e,⟨0,by omega⟩)) a := by
  let l : TypeLink K E := (e,⟨0,by omega⟩)
  have h0 : l.2.val = 0 := rfl
  have h4 : l.2.val ≠ 4*K := by dsimp [l]; omega
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_internal K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_zero K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_internal K l h4 (fun t => I.horizontalSum K t a ys)
  ext v
  have hv := Set.ext_iff.mp he (v + I.biasSrc e)
  simp only [I.mem_attainable_image] at hv
  simp only [hl,hr'] at hv
  have h4' : (0 : ℕ) ≠ 4*K := by omega
  unfold siteRing at hv
  simp only [linkLeft,linkRight,l,linkBias] at hv
  simp only [dite_eq_right h4'] at hv
  constructor
  · rintro ⟨x,⟨hh,ys,hys,rfl⟩,heq⟩
    have heq' : I.linearSrc e (I.horizontalSum K (.inl (I.src e)) a ys) = v+I.biasSrc e := by
      rw [← heq,affineSrc,add_assoc,CharTwo.add_self_eq_zero,add_zero]
    obtain ⟨hh',zs,hzs,hz⟩ := hv.mp ⟨hh,ys,hys,heq'⟩
    exact ⟨hh',zs,hzs,add_right_cancel hz⟩
  · rintro ⟨hh,zs,hzs,hz⟩
    obtain ⟨hh',ys,hys,hy⟩ := hv.mpr ⟨hh,zs,hzs,congrArg (fun z : F₂ => z + I.biasSrc e) hz⟩
    refine ⟨_,⟨hh',ys,hys,rfl⟩,?_⟩
    rw [affineSrc,hy,add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem attainable_internal (K : ℕ) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) (j : Fin (4*K)) (hj : j.val+1 < 4*K) :
    I.Attainable K (.inr (e,j)) a =
      I.Attainable K (.inr (e,⟨j.val+1,hj⟩)) a := by
  let l : TypeLink K E := (e,⟨j.val+1,by omega⟩)
  have h0 : l.2.val ≠ 0 := by dsimp [l]; omega
  have h4 : l.2.val ≠ 4*K := by dsimp [l]; omega
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_internal K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_internal K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_internal K l h4 (fun t => I.horizontalSum K t a ys)
  ext v
  have hv := Set.ext_iff.mp he v
  simp only [I.mem_attainable_image,hl,hr',linkBias,ite_eq_right h0,ite_eq_right h4,add_zero] at hv
  unfold siteRing at hv
  simp only [linkLeft,dite_eq_right h0,linkRight,dite_eq_right h4] at hv
  simp only [Attainable,Set.mem_ofPred_eq]
  unfold siteRing
  dsimp only [l] at hv
  simp only [Nat.add_sub_cancel] at hv
  exact hv

theorem attainable_last (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) :
    I.Attainable K (.inr (e,⟨4*K-1,by omega⟩)) a =
      I.affineDst e '' I.Attainable K (.inl (I.dst e)) (I.permuteAddress e a) := by
  let l : TypeLink K E := (e,⟨4*K,by omega⟩)
  have h0 : l.2.val ≠ 0 := by dsimp [l]; omega
  have h4 : l.2.val = 4*K := rfl
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_last K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_internal K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_last K l h4 (fun t => I.horizontalSum K t (I.permuteAddress l.1 a) ys)
  ext v
  have hv := Set.ext_iff.mp he v
  simp only [I.mem_attainable_image,hl,hr',linkBias,ite_eq_right h0,ite_eq_left h4] at hv
  unfold siteRing at hv
  simp only [linkLeft,dite_eq_right h0,linkRight,dite_eq_left h4] at hv
  rw [I.mem_attainable_image K (.inl (I.dst e)) (I.permuteAddress e a) (I.affineDst e) v]
  simp only [Attainable,Set.mem_ofPred_eq,affineDst]
  unfold siteRing
  dsimp only [l] at hv
  exact hv

theorem attainable_internal_all (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) (j : Fin (4*K)) :
    I.Attainable K (.inr (e,⟨0,by omega⟩)) a = I.Attainable K (.inr (e,j)) a := by
  have aux (n : ℕ) (hn : n < 4*K) :
      I.Attainable K (.inr (e,⟨0,by omega⟩)) a = I.Attainable K (.inr (e,⟨n,hn⟩)) a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (ih (by omega)).trans (I.attainable_internal K hr e a ha ⟨n,by omega⟩ hn)
  exact aux j.val j.isLt

theorem colored_wins_ac (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r)
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none)) : I.ArcConsistent := by
  refine ⟨fun p a => I.Attainable K (.inl p) a,?_,?_⟩
  · intro p a
    exact I.attainable_nonempty K h (.inl p) a (fun _ => True.intro)
  · intro e a ha
    rw [← I.permuteAddress_eq e a ha]
    exact (I.attainable_first K hK hr e a ha).trans
      ((I.attainable_internal_all K hK hr e a ha ⟨4*K-1,by omega⟩).trans
        (I.attainable_last K hK hr e a ha))

theorem colored_wins_iff_ac (hr : 2 ≤ r) :
    Pebble.Wins (I.valuationGraph (r+2) 0) (I.valuationGraph (r+2) 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  constructor
  · exact I.colored_wins_ac (r+2) (by omega) (by omega)
  · intro h
    obtain ⟨Q⟩ := I.arcConsistent_iff.mp h
    exact I.ac_colored_wins Q (r+2) (by omega) hr le_rfl

end ConsistencyData
end WLTime.Compression

namespace WLTime.Marking

inductive Vertex (V : Type uV) (count : V → ℕ) (q : ℕ) where
  | base : V → Vertex V count q
  | mark : (v : V) → Fin (count v) → Vertex V count q
  | hub : Vertex V count q
  | pad : Fin q → Vertex V count q
  deriving DecidableEq, Fintype

variable {V : Type uV} {W : Type uW} {D : Type uD} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}

def Adj (G : SimpleGraph V) : Vertex V count q → Vertex V count q → Prop
  | .base x, .base y => G.Adj x y
  | .base x, .mark y _ => x = y
  | .mark x _, .base y => x = y
  | .hub, .hub => False
  | .hub, _ => True
  | _, .hub => True
  | _, _ => False

def graph (G : SimpleGraph V) (count : V → ℕ) (q : ℕ) : SimpleGraph (Vertex V count q) where
  Adj := Adj G
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp only [Adj] at h ⊢ <;> first | exact G.symm h | exact h.symm⟩
  loopless := ⟨by intro x; cases x <;> simp only [Adj,SimpleGraph.irrefl,not_false_eq_true]⟩

theorem diameter_two (G : SimpleGraph V) (x y : Vertex V count q) :
    x = y ∨ (graph G count q).Adj x y ∨
      ∃ z, (graph G count q).Adj x z ∧ (graph G count q).Adj z y := by
  cases x <;> cases y <;> simp only [graph,Adj] <;> try tauto
  all_goals exact Or.inr (Or.inr ⟨.hub,True.intro,True.intro⟩)

@[simp] theorem mark_eq_iff (v w : V) (i : Fin (count v)) (j : Fin (count w)) :
    (Vertex.mark v i : Vertex V count q) = .mark w j ↔ v=w ∧ i.val=j.val := by
  constructor
  · intro h
    cases h
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,h⟩
    exact congrArg (Vertex.mark v) (Fin.ext h)

noncomputable def liftEquiv (e : V ≃ W) (hc : ∀ v, count v = count' (e v)) :
    Vertex V count q ≃ Vertex W count' q where
  toFun
    | .base v => .base (e v)
    | .mark v i => .mark (e v) ⟨i.val,by rw [← hc v]; exact i.isLt⟩
    | .hub => .hub
    | .pad i => .pad i
  invFun
    | .base w => .base (e.symm w)
    | .mark w i => .mark (e.symm w) ⟨i.val,by rw [hc (e.symm w),e.apply_symm_apply]; exact i.isLt⟩
    | .hub => .hub
    | .pad i => .pad i
  left_inv x := by cases x <;> simp only [e.symm_apply_apply,mark_eq_iff,and_self]
  right_inv x := by cases x <;> simp only [e.apply_symm_apply,mark_eq_iff,and_self]

def tag (c : V → D) : Vertex V count q → Option D
  | .base x => some (c x)
  | .mark x _ => some (c x)
  | .hub => none
  | .pad _ => none

def Maps {S : Type uS} (maps : S → V → W → Prop) (s : S) :
    Vertex V count q → Vertex W count' q → Prop
  | .base v, .base w => maps s v w
  | .mark v i, .mark w j => maps s v w ∧ i.val=j.val
  | .hub, .hub => True
  | .pad i, .pad j => i=j
  | _, _ => False

theorem maps_atomic {S : Type uS} {G : SimpleGraph V} {H : SimpleGraph W}
    {maps : S → V → W → Prop} (s : S)
    (ha : ∀ {x u y v}, maps s x y → maps s u v →
      (x=u ↔ y=v) ∧ (G.Adj x u ↔ H.Adj y v))
    {x u : Vertex V count q} {y v : Vertex W count' q}
    (hx : Maps maps s x y) (hu : Maps maps s u v) :
    (x=u ↔ y=v) ∧ ((graph G count q).Adj x u ↔ (graph H count' q).Adj y v) := by
  cases x <;> cases y <;> simp only [Maps] at hx <;> try contradiction
  all_goals cases u <;> cases v <;> simp only [Maps] at hu <;> try contradiction
  all_goals simp only [graph,Adj,Vertex.base.injEq,Vertex.pad.injEq,mark_eq_iff,
    reduceCtorEq,and_true,true_and]
  · exact ha hx hu
  · exact (ha hx hu.1).1
  · exact (ha hx.1 hu).1
  · exact and_congr (ha hx.1 hu.1).1 (by rw [hx.2,hu.2])
  · rw [hx,hu]

noncomputable def liftSystem {G : SimpleGraph V} {H : SimpleGraph W}
    (c : V → D) (d : W → D) (n : D → ℕ) (q K : ℕ)
    (L : Pebble.ExactLocalSystem.{uV, uW, uD, uState}
      G H (fun v w => c v = d w) (fun v => some (c v)) K) :
    Pebble.ExactLocalSystem (graph G (n ∘ c) q) (graph H (n ∘ d) q)
      (fun _ _ => True) (tag c) K where
  State := L.State
  family := L.family
  agree := L.agree
  maps := Maps L.maps
  empty := L.empty
  restrict := L.restrict
  extend := L.extend
  transfer := by
    intro U R S x y hag hxy hxU
    cases x <;> cases y <;> simp only [Maps] at hxy ⊢ <;> try contradiction
    · exact L.transfer hag hxy (fun b hb => hxU b hb)
    · exact ⟨L.transfer hag hxy.1 (fun b hb => hxU b hb),hxy.2⟩
    · exact hxy
  color := by intro R x y h; trivial
  atomic := fun hx hu => maps_atomic _ (fun h₁ h₂ => L.atomic h₁ h₂) hx hu
  assemble a ha := liftEquiv (L.assemble a ha) (fun x => congrArg n
    (L.color (L.assemble_some a ha x (c x) rfl)))
  assemble_some := by
    intro a ha x b hb
    cases x with
    | base x => exact L.assemble_some a ha x b hb
    | mark x i => exact ⟨L.assemble_some a ha x b hb,rfl⟩
    | hub => cases hb
    | pad i => cases hb
  assemble_none := by
    intro a ha x hb R
    cases x with
    | base x => cases hb
    | mark x i => cases hb
    | hub => trivial
    | pad i => rfl

end WLTime.Marking

namespace WLTime.Marking
variable {V : Type uV} (count : V → ℕ) (q : ℕ)

def equivSum : Vertex V count q ≃ (V ⊕ (Σ v,Fin (count v))) ⊕ (Unit ⊕ Fin q) where
  toFun
    | .base v => .inl (.inl v)
    | .mark v i => .inl (.inr ⟨v,i⟩)
    | .hub => .inr (.inl ())
    | .pad i => .inr (.inr i)
  invFun
    | .inl (.inl v) => .base v
    | .inl (.inr ⟨v,i⟩) => .mark v i
    | .inr (.inl _) => .hub
    | .inr (.inr i) => .pad i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (x | ⟨v,i⟩) | (_ | i) <;> rfl

theorem card_vertices [Fintype V] :
    Fintype.card (Vertex V count q) = Fintype.card V + ∑ v, count v + 1 + q := by
  rw [Fintype.card_congr (equivSum count q)]
  simp [add_assoc]

theorem sum_vertices [Fintype V] (f : Vertex V count q → ℕ) :
    ∑ x, f x = (∑ v, f (.base v)) + (∑ v, ∑ i, f (.mark v i)) + f .hub + ∑ i, f (.pad i) := by
  rw [← (equivSum count q).symm.sum_comp f]
  simp [equivSum,Fintype.sum_sum_type,Fintype.sum_sigma,add_assoc]

open scoped Classical in
theorem degree_base [Fintype V] (G : SimpleGraph V) (x : V) :
    Pebble.degree (graph G count q) (.base x) = Pebble.degree G x + count x + 1 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  unfold graph Adj
  simp [Finset.sum_boole,add_assoc,apply_ite Finset.card]

open scoped Classical in
theorem degree_mark [Fintype V] (G : SimpleGraph V) (x : V) (i : Fin (count x)) :
    Pebble.degree (graph G count q) (.mark x i) = 2 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  unfold graph Adj
  simp

open scoped Classical in
theorem degree_pad [Fintype V] (G : SimpleGraph V) (i : Fin q) :
    Pebble.degree (graph G count q) (.pad i) = 1 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  simp [graph,Adj]

open scoped Classical in
theorem degree_hub [Fintype V] (G : SimpleGraph V) :
    Pebble.degree (graph G count q) .hub = Fintype.card V + ∑ v, count v + q := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  simp [graph,Adj]

end WLTime.Marking

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

open scoped Classical in
theorem base_degree_lt (G : SimpleGraph V) (x : V) : Pebble.degree G x < Fintype.card V := by
  have h := G.degree_lt_card_verts x
  rwa [← SimpleGraph.card_neighborSet_eq_degree] at h

theorem sum_count_gt (count : V → ℕ) (x : V)
    (hN : 2 ≤ Fintype.card V) (hpos : ∀ v, 0 < count v) : count x < ∑ v, count v := by
  classical
  have hne : ∃ y : V, y ≠ x := by
    by_contra h
    push Not at h
    have hcard : Fintype.card V ≤ 1 := Fintype.card_le_of_injective
      (fun _ : V => ()) (by intro a b _; exact (h a).trans (h b).symm)
    omega
  obtain ⟨y,hy⟩ := hne
  have hb : count y ≤ ∑ v ∈ Finset.univ.erase x, count v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hy])
  have he := Finset.sum_erase_add Finset.univ count (Finset.mem_univ x)
  have hp := hpos y
  omega

theorem hub_above_base (G : SimpleGraph V) (count : V → ℕ) (q : ℕ)
    (hN : 2 ≤ Fintype.card V) (hpos : ∀ v, 0 < count v) (x : V) :
    Pebble.degree (graph G count q) (.base x) < Pebble.degree (graph G count q) .hub := by
  rw [degree_base,degree_hub]
  have hsum := sum_count_gt count x hN hpos
  have hg := base_degree_lt G x
  omega

theorem code_of_degree {N j l dg dh : ℕ} (hg : dg < N) (hh : dh < N)
    (he : dg + j*(N+1)+1 = dh + l*(N+1)+1) : j=l := by
  rcases lt_trichotomy j l with h | h | h
  · have hm := Nat.mul_le_mul_right (N+1) (show j+1 ≤ l by omega)
    nlinarith
  · exact h
  · have hm := Nat.mul_le_mul_right (N+1) (show l+1 ≤ j by omega)
    nlinarith

end WLTime.Marking

end OAI
