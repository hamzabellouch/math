import OAI.Computability.WeisfeilerLeman.Readouts

namespace OAI

universe uA uB uD uState

namespace WLTime.Pebble

abbrev Position (K : ℕ) (A : Type uA) (B : Type uB) := Fin K → Option (A × B)

def Position.Sub {K : ℕ} {A : Type uA} {B : Type uB} (P Q : Position K A B) : Prop :=
  ∀ i, P i = none ∨ P i = Q i

def Position.PartialIso {K : ℕ} {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (P : Position K A B) : Prop :=
  (∀ i x y, P i = some (x,y) → C x y) ∧
  ∀ i j x y u v, P i = some (x,y) → P j = some (u,v) →
    (x = u ↔ y = v) ∧ (G.Adj x u ↔ H.Adj y v)

structure Invariant {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (K : ℕ) where
  safe : Position K A B → Prop
  forget : ∀ {P Q}, safe Q → P.Sub Q → safe P
  atomic : ∀ {P}, safe P → P.PartialIso G H C
  extend : ∀ {P}, safe P → ∀ i, P i = none →
    ∃ e : A ≃ B, ∀ z, safe (Function.update P i (some (z,e z)))

def Wins {K : ℕ} {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (P : Position K A B) : Prop :=
  ∃ I : Invariant G H C K, I.safe P

namespace Position
variable {K : ℕ} {A : Type uA} {B : Type uB}

theorem Sub.refl (P : Position K A B) : P.Sub P := fun _ => Or.inr rfl

theorem Sub.trans {P Q R : Position K A B} (hPQ : P.Sub Q) (hQR : Q.Sub R) : P.Sub R := by
  intro i
  rcases hPQ i with h | h
  · exact Or.inl h
  · rcases hQR i with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')

theorem Sub.mark {P Q : Position K A B} (h : P.Sub Q) {i : Fin K} {x : A} {y : B}
    (hi : P i = some (x,y)) : Q i = some (x,y) := by
  rcases h i with h | h
  · simp only [hi, Option.some_ne_none] at h
  · exact h.symm.trans hi

theorem erase_sub (P : Position K A B) (i : Fin K) : Position.Sub (Function.update P i none) P := by
  intro j
  by_cases h : j = i
  · subst j; exact Or.inl (Function.update_self i none P)
  · exact Or.inr (Function.update_of_ne h none P)

end Position

namespace Wins
variable {K : ℕ} {A : Type uA} {B : Type uB} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {P Q : Position K A B}

theorem forget (h : Wins G H C Q) (hPQ : P.Sub Q) : Wins G H C P := by
  obtain ⟨I,hI⟩ := h
  exact ⟨I,I.forget hI hPQ⟩

theorem atomic (h : Wins G H C P) : P.PartialIso G H C := by
  obtain ⟨I,hI⟩ := h
  exact I.atomic hI

theorem extend (h : Wins G H C P) (i : Fin K) (hi : P i = none) :
    ∃ e : A ≃ B, ∀ z, Wins G H C (Function.update P i (some (z,e z))) := by
  obtain ⟨I,hI⟩ := h
  obtain ⟨e,he⟩ := I.extend hI i hi
  exact ⟨e,fun z => ⟨I,he z⟩⟩

theorem erase (h : Wins G H C P) (i : Fin K) : Wins G H C (Function.update P i none) :=
  h.forget (P.erase_sub i)

theorem rename (h : Wins G H C P) (e : Equiv.Perm (Fin K)) :
    Wins G H C (fun i => P (e i)) := by
  classical
  obtain ⟨I,hI⟩ := h
  let J : Invariant G H C K := {
    safe := fun Q => I.safe (fun i => Q (e.symm i))
    forget := by
      intro Q R hR hQR
      exact I.forget hR (fun i => hQR (e.symm i))
    atomic := by
      intro Q hQ
      obtain ⟨hc,ha⟩ := I.atomic hQ
      constructor
      · intro i x y hi
        exact hc (e i) x y (by simpa using hi)
      · intro i j x y u v hi hj
        exact ha (e i) (e j) x y u v (by simpa using hi) (by simpa using hj)
    extend := by
      intro Q hQ i hi
      obtain ⟨f,hf⟩ := I.extend hQ (e i) (by simpa using hi)
      refine ⟨f,fun z => ?_⟩
      have heq : (fun j => (Function.update Q i (some (z,f z))) (e.symm j)) =
          Function.update (fun j => Q (e.symm j)) (e i) (some (z,f z)) := by
        funext j
        by_cases hj : j = e i
        · subst j; simp
        · have hji : e.symm j ≠ i := by intro hh; exact hj (by simpa using congrArg e hh)
          simp only [Function.update_of_ne hj, Function.update_of_ne hji]
      rw [heq]
      exact hf z }
  exact ⟨J,by simpa only [J, Equiv.apply_symm_apply] using hI⟩

end Wins

noncomputable def active {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D)
    (P : Position K A B) : Finset D := by
  classical
  exact Finset.univ.biUnion fun i => match P i with
    | none => ∅
    | some (x,_) => (tag x).toFinset

open scoped Classical in
theorem mem_active {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B) (d : D) :
    d ∈ active tag P ↔ ∃ i x y, P i = some (x,y) ∧ tag x = some d := by
  simp only [active, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hi⟩
    cases hp : P i with
    | none => simp only [hp, Finset.notMem_empty] at hi
    | some xy =>
      rcases xy with ⟨x,y⟩
      simp only [hp, Option.mem_toFinset] at hi
      exact ⟨i,x,y,hp,hi⟩
  · rintro ⟨i,x,y,hp,ht⟩
    exact ⟨i,by simp [hp,ht]⟩

theorem active_mono {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D)
    {P Q : Position K A B} (h : P.Sub Q) : active tag P ⊆ active tag Q := by
  intro d hd
  obtain ⟨i,x,y,hi,ht⟩ := (mem_active tag P d).mp hd
  exact (mem_active tag Q d).mpr ⟨i,x,y,h.mark hi,ht⟩

theorem active_card_le {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (S : Finset (Fin K)) (hS : ∀ i, P i ≠ none → i ∈ S) : (active tag P).card ≤ S.card := by
  classical
  have heq : active tag P = S.biUnion (fun i => match P i with
      | none => ∅
      | some (x,_) => (tag x).toFinset) := by
    ext d
    simp only [mem_active, Finset.mem_biUnion]
    constructor
    · rintro ⟨i,x,y,hi,ht⟩
      exact ⟨i,hS i (by simp [hi]),by simp [hi,ht]⟩
    · rintro ⟨i,_,hi⟩
      cases hp : P i with
      | none => simp only [hp,Finset.notMem_empty] at hi
      | some xy =>
        rcases xy with ⟨x,y⟩
        exact ⟨i,x,y,hp,by simpa only [hp,Option.mem_toFinset,Option.mem_def] using hi⟩
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, (match P i with | none => ∅ | some (x,_) => (tag x).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      cases P i with
      | none => simp
      | some xy => cases hh : tag xy.1 <;> simp [hh]
    _ = S.card := by simp

theorem active_card {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B) :
    (active tag P).card ≤ K := by
  simpa using active_card_le tag P Finset.univ (fun i _ => Finset.mem_univ i)

theorem active_card_free {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (i : Fin K) (hi : P i = none) : (active tag P).card < K := by
  have h := active_card_le tag P (Finset.univ.erase i) (by
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro he; subst j; exact hj hi)
  have hcard : (Finset.univ.erase i).card = K-1 := by simp
  rw [hcard] at h
  have := i.isLt
  omega

open scoped Classical in
theorem active_update {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (i : Fin K) (hi : P i = none) (x : A) (y : B) :
    active tag (Function.update P i (some (x,y))) = active tag P ∪ (tag x).toFinset := by
  ext d
  simp only [mem_active,Finset.mem_union,Option.mem_toFinset]
  constructor
  · rintro ⟨j,u,v,hj,ht⟩
    by_cases he : j = i
    · subst j
      simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
      exact Or.inr (hj.1 ▸ ht)
    · rw [Function.update_of_ne he] at hj
      exact Or.inl ⟨j,u,v,hj,ht⟩
  · rintro (⟨j,u,v,hj,ht⟩ | ht)
    · have he : j ≠ i := by intro he; subst j; simp [hi] at hj
      exact ⟨j,u,v,by simpa only [Function.update_of_ne he] using hj,ht⟩
    · exact ⟨i,x,y,Function.update_self _ _ _,ht⟩

end WLTime.Pebble

namespace WLTime.Pebble

structure ExactLocalSystem {A : Type uA} {B : Type uB} {D : Type uD} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (tag : A → Option D) (K : ℕ) where
  State : Type uState
  family : Finset D → State → Prop
  agree : Finset D → State → State → Prop
  maps : State → A → B → Prop
  empty : ∃ R, family ∅ R
  restrict : ∀ {U V}, V ⊆ U → U.card ≤ K → ∀ {R}, family U R → family V R
  extend : ∀ {U V}, V ⊆ U → U.card ≤ K → ∀ {R}, family V R →
    ∃ R', family U R' ∧ agree V R R'
  transfer : ∀ {U R S x y}, agree U R S → maps R x y →
    (∀ d, tag x = some d → d ∈ U) → maps S x y
  color : ∀ {R x y}, maps R x y → C x y
  atomic : ∀ {R x y u v}, maps R x y → maps R u v →
    (x = u ↔ y = v) ∧ (G.Adj x u ↔ H.Adj y v)
  assemble : (a : D → State) → (∀ d, family {d} (a d)) → A ≃ B
  assemble_some : ∀ a ha x d, tag x = some d → maps (a d) x (assemble a ha x)
  assemble_none : ∀ a ha x, tag x = none → ∀ R, maps R x (assemble a ha x)

namespace ExactLocalSystem
variable {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {tag : A → Option D}
    (S : ExactLocalSystem.{uA, uB, uD, uState} G H C tag K)

def Safe (P : Position K A B) : Prop :=
  ∃ R, S.family (active tag P) R ∧ ∀ i x y, P i = some (x,y) → S.maps R x y

noncomputable def invariant : Invariant G H C K where
  safe := S.Safe
  forget := by
    intro P Q hQ hPQ
    obtain ⟨R,hR,heq⟩ := hQ
    exact ⟨R,S.restrict (active_mono tag hPQ) (active_card tag Q) hR,
      fun i x y hi => heq i x y (hPQ.mark hi)⟩
  atomic := by
    intro P hP
    obtain ⟨R,hR,heq⟩ := hP
    exact ⟨fun i x y hi => S.color (heq i x y hi),
      fun i j x y u v hi hj => S.atomic (heq i x y hi) (heq j u v hj)⟩
  extend := by
    classical
    intro P hP i hi
    obtain ⟨R,hR,heq⟩ := hP
    let U := active tag P
    have hcard : U.card < K := active_card_free tag P i hi
    have hext (d : D) : ∃ R', S.family (insert d U) R' ∧ S.agree U R R' :=
      S.extend (Finset.subset_insert d U)
        ((Finset.card_insert_le d U).trans (by omega)) hR
    choose a ha hkeep using hext
    have hsingle (d : D) : S.family {d} (a d) :=
      S.restrict (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self d U))
        ((Finset.card_insert_le d U).trans (by omega)) (ha d)
    refine ⟨S.assemble a hsingle, fun z => ?_⟩
    cases ht : tag z with
    | none =>
      refine ⟨R, ?_, ?_⟩
      · simpa only [active_update tag P i hi,ht,Option.toFinset_none,Finset.union_empty] using hR
      · intro j x y hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
          rcases hj with ⟨rfl,rfl⟩
          exact S.assemble_none a hsingle z ht R
        · rw [Function.update_of_ne hji] at hj
          exact heq j x y hj
    | some d =>
      refine ⟨a d, ?_, ?_⟩
      · simpa only [active_update tag P i hi,ht,Option.toFinset_some,Finset.union_singleton] using ha d
      · intro j x y hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
          rcases hj with ⟨rfl,rfl⟩
          exact S.assemble_some a hsingle z d ht
        · rw [Function.update_of_ne hji] at hj
          exact S.transfer (hkeep d) (heq j x y hj)
            (fun b hb => (mem_active tag P b).mpr ⟨j,x,y,hj,hb⟩)

include S in
theorem wins_empty : Wins G H C (fun _ : Fin K => none) := by
  obtain ⟨R,hR⟩ := S.empty
  refine ⟨S.invariant,R,?_,?_⟩
  · have he : active tag (fun _ : Fin K => (none : Option (A×B))) = ∅ := by
      classical
      ext d
      simp [mem_active]
    rw [he]
    exact hR
  · intro i x y hi
    simp at hi

end ExactLocalSystem
end WLTime.Pebble

namespace WLTime.Pebble.Wins
variable {K : ℕ} {A : Type uA} {B : Type uB} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {P : Position K A B}

theorem replace (h : Wins G H C P) (i s : Fin K) (his : i ≠ s) (hs : P s = none) (x : A) :
    ∃ y, Wins G H C (Function.update P i (some (x,y))) ∧ C x y ∧
      ∀ u v, P i = some (u,v) → (u = x ↔ v = y) ∧ (G.Adj u x ↔ H.Adj v y) := by
  classical
  obtain ⟨e,he⟩ := h.extend s hs
  have hQ := he x
  refine ⟨e x, ?_, hQ.atomic.1 s x (e x) (Function.update_self _ _ _), ?_⟩
  · have hR := (hQ.erase i).rename (Equiv.swap i s)
    have heq : (fun j => Function.update (Function.update P s (some (x,e x))) i none
        ((Equiv.swap i s) j)) = Function.update P i (some (x,e x)) := by
      funext j
      by_cases hji : j = i
      · subst j; simp [his.symm]
      · by_cases hjs : j = s
        · subst j; simp [his.symm,hs]
        · simp [Equiv.swap_apply_of_ne_of_ne hji hjs,hji,hjs]
    rw [heq] at hR
    exact hR
  · intro u v hi
    exact hQ.atomic.2 i s u v x (e x)
      (by simpa only [Function.update_of_ne his] using hi) (Function.update_self _ _ _)

theorem realize (h : Wins G H C (fun _ : Fin K => none)) (X : Fin K → Option A) :
    ∃ P : Position K A B, Wins G H C P ∧ ∀ i, (P i).map Prod.fst = X i := by
  classical
  have aux (S : Finset (Fin K)) : ∃ P : Position K A B, Wins G H C P ∧
      (∀ i ∈ S, (P i).map Prod.fst = X i) ∧ (∀ i ∉ S, P i = none) := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => none,h,by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨Q,hQ,hqin,hqout⟩ := ih
      cases hx : X i with
      | none =>
        refine ⟨Q,hQ,?_,fun j hj => hqout j (fun h => hj (Finset.mem_insert_of_mem h))⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hqout j hi,Option.map_none] using hx.symm
        · exact hqin j hj
      | some x =>
        obtain ⟨e,he⟩ := hQ.extend i (hqout i hi)
        refine ⟨Function.update Q i (some (x,e x)),he x,?_,?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simp only [Function.update_self,Option.map_some,hx]
          · have hji : j ≠ i := by intro hh; subst j; exact hi hj
            simpa only [Function.update_of_ne hji] using hqin j hj
        · intro j hj
          have hji : j ≠ i := by intro hh; subst j; exact hj (Finset.mem_insert_self i S)
          rw [Function.update_of_ne hji]
          exact hqout j (fun hh => hj (Finset.mem_insert_of_mem hh))
  obtain ⟨P,hP,hin,_⟩ := aux Finset.univ
  exact ⟨P,hP,fun i => hin i (Finset.mem_univ i)⟩

end WLTime.Pebble.Wins

namespace WLTime.Pebble

noncomputable def degree {A : Type uA} [Fintype A] (G : SimpleGraph A) (x : A) : ℕ :=
  by classical exact Fintype.card {z : A // G.Adj x z}

theorem Wins.neighborhood_bijection {K : ℕ} {A : Type uA} {B : Type uB}
    {G : SimpleGraph A} {H : SimpleGraph B} {C : A → B → Prop}
    (hK : 2 ≤ K) {P : Position K A B} (hP : Wins G H C P)
    {i : Fin K} {x : A} {y : B} (hi : P i = some (x,y)) :
    ∃ e : A ≃ B, e x = y ∧ ∀ z, G.Adj x z ↔ H.Adj y (e z) := by
  classical
  let j : Fin K := if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    by_cases h0 : i.val=0
    · simp only [j,ite_eq_left h0,Fin.val_mk] at hh
      omega
    · simp only [j,ite_eq_right h0,Fin.val_mk] at hh
      exact h0 hh
  let Q : Position K A B := fun a => if a=i then P a else none
  have hQ : Wins G H C Q := hP.forget (fun a => by
    by_cases ha : a=i
    · exact Or.inr (ite_eq_left ha)
    · exact Or.inl (ite_eq_right ha))
  obtain ⟨e,he⟩ := hQ.extend j (ite_eq_right hij.symm)
  have hat (z : A) := (he z).atomic.2 i j x y z (e z)
    (by simp only [Function.update_of_ne hij,Q,hi,ite_true])
    (Function.update_self _ _ _)
  exact ⟨e,((hat x).1.mp rfl).symm,fun z => (hat z).2⟩

theorem Wins.degree_eq {K : ℕ} {A : Type uA} {B : Type uB} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} {C : A → B → Prop}
    (hK : 2 ≤ K) {P : Position K A B} (hP : Wins G H C P)
    {i : Fin K} {x : A} {y : B} (hi : P i = some (x,y)) :
    degree G x = degree H y := by
  classical
  obtain ⟨e,_,he⟩ := hP.neighborhood_bijection hK hi
  exact Fintype.card_congr (Equiv.subtypeEquiv e he)

end WLTime.Pebble

end OAI
