import OAI.ModelTheory.Choiceless.Interpretations

namespace OAI

noncomputable section

namespace CPTSeparation.Interpretations

section

open Classical Finset Hereditary

variable {R T A B : Type} {S S' : Structure R} (I : Interpretation R T)

theorem map_payload (e : S.Iso S') (f : A → B) (c : S.Carrier → HF A)
    (c' : S'.Carrier → HF B) (hc : ∀ a, map f (c a) = c' (e.equiv a)) (C : I.Vertex S) :
    map f (payload I S c C) = payload I S' c' (I.vertexEquiv e C) := by
  rw [payload,map_ofFinset,payload]
  apply ofFinset_inj.mpr
  ext z
  simp only [image_image,mem_image,mem_filter,mem_univ,true_and,Function.comp_apply]
  constructor
  · rintro ⟨a,ha,hz⟩
    refine ⟨I.domainEquiv e a,?_,?_⟩
    · exact congrArg (I.vertexEquiv e) ha
    · simpa only [map_pair,hc,Interpretation.domainEquiv_val] using hz
  · rintro ⟨a,ha,hz⟩
    obtain ⟨a,rfl⟩ := (I.domainEquiv e).surjective a
    refine ⟨a,(I.vertexEquiv e).injective ha,?_⟩
    simpa only [map_pair,hc,Interpretation.domainEquiv_val] using hz

theorem map_vertexCode (e : S.Iso S') (f : A → B) (c : S.Carrier → HF A)
    (c' : S'.Carrier → HF B) (hc : ∀ a, map f (c a) = c' (e.equiv a)) (j : ℕ) (C : I.Vertex S) :
    map f (vertexCode I S c j C) = vertexCode I S' c' j (I.vertexEquiv e C) := by
  simp only [vertexCode,map_pair,map_ordinal,map_payload I e f c c' hc]

private theorem map_mem_wrappers (f : A → B) {a b x : HF A} (hx : x ∈ wrappers a b) :
    map f x ∈ wrappers (map f a) (map f b) := by
  simp only [wrappers,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases hx with rfl|rfl|rfl <;> simp

theorem map_mem_pairFamily (e : S.Iso S') (f : A → B) (c : S.Carrier → HF A)
    (c' : S'.Carrier → HF B) (hc : ∀ a, map f (c a) = c' (e.equiv a))
    {x : HF A} (hx : x ∈ pairFamily I S c) : map f x ∈ pairFamily I S' c' := by
  obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx
  apply mem_biUnion.mpr
  refine ⟨I.domainEquiv e p,mem_univ _,?_⟩
  simpa only [hc,Interpretation.domainEquiv_val] using map_mem_wrappers f hp

theorem map_mem_classFamily (e : S.Iso S') (f : A → B) (c : S.Carrier → HF A)
    (c' : S'.Carrier → HF B) (hc : ∀ a, map f (c a) = c' (e.equiv a))
    (j : ℕ) {x : HF A} (hx : x ∈ classFamily I S c j) : map f x ∈ classFamily I S' c' j := by
  obtain ⟨C,_,hC⟩ := mem_biUnion.mp hx
  apply mem_biUnion.mpr
  refine ⟨I.vertexEquiv e C,mem_univ _,?_⟩
  rcases mem_insert.mp hC with rfl|hC
  · rw [map_payload I e f c c' hc]
    exact mem_insert_self _ _
  · apply mem_insert_of_mem
    simpa only [map_payload I e f c c' hc,map_ordinal] using map_mem_wrappers f hC

namespace Program

variable {R : Type} (P : Program R) (S : Structure R)

def stateIso {S' : Structure R} (e : S.Iso S') : (j : ℕ) → (P.state S j).Iso (P.state S' j)
  | 0 => P.init.applyIso e
  | j+1 => P.step.applyIso (stateIso e j)

def code : (j : ℕ) → (P.state S j).Carrier → HF S.Carrier
  | 0 => vertexCode P.init S atom 1
  | j+1 => vertexCode P.step (P.state S j) (code j) (j+2)

theorem code_injective (j : ℕ) : Function.Injective (P.code S j) := by
  induction j with
  | zero => exact vertexCode_injective _ _ _ atom_injective _
  | succ j ih => exact vertexCode_injective _ _ _ ih _

theorem map_code {S' : Structure R} (e : S.Iso S') (j : ℕ) (a : (P.state S j).Carrier) :
    map e.equiv (P.code S j a) = P.code S' j ((P.stateIso S e j).equiv a) := by
  induction j with
  | zero => exact map_vertexCode P.init e e.equiv atom atom (fun a => map_atom _ _) _ a
  | succ j ih =>
    exact map_vertexCode P.step (P.stateIso S e j) e.equiv
      (P.code S j) (P.code S' j) ih _ a

def baseFamily (B : ℕ) : Finset (HF S.Carrier) :=
  univ.image atom ∪ (range (B+1)).image ordinal

def family (B : ℕ) : ℕ → Finset (HF S.Carrier)
  | 0 => baseFamily S B
  | j+1 => match j with
    | 0 => family B 0 ∪ pairFamily P.init S atom ∪ classFamily P.init S atom 1
    | k+1 => family B (k+1) ∪ pairFamily P.step (P.state S k) (P.code S k) ∪
        classFamily P.step (P.state S k) (P.code S k) (k+2)

theorem family_mono (B j : ℕ) : P.family S B j ⊆ P.family S B (j+1) := by
  cases j <;> exact fun x hx => mem_union_left _ (mem_union_left _ hx)

theorem base_subset_family (B j : ℕ) : baseFamily S B ⊆ P.family S B j := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih => exact ih.trans (P.family_mono S B j)

theorem atom_mem_family (B j : ℕ) (a : S.Carrier) : atom a ∈ P.family S B j :=
  P.base_subset_family S B j (mem_union_left _ (mem_image.mpr ⟨a,mem_univ _,rfl⟩))

theorem ordinal_mem_family (B j i : ℕ) (hi : i ≤ B) : ordinal i ∈ P.family S B j :=
  P.base_subset_family S B j (mem_union_right _ (mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩))

theorem code_mem_family (B j : ℕ) (a : (P.state S j).Carrier) : P.code S j a ∈ P.family S B (j+1) := by
  have memC {U V : Type} (I : Interpretation U V) (T : Structure U)
      (c : T.Carrier → HF S.Carrier) (i : ℕ) (C : I.Vertex T) :
      vertexCode I T c i C ∈ classFamily I T c i := by
    exact mem_biUnion.mpr ⟨C,mem_univ _,mem_insert_of_mem (by simp [vertexCode,wrappers])⟩
  cases j with
  | zero => exact mem_union_right _ (memC _ _ _ _ _)
  | succ j => exact mem_union_right _ (memC _ _ _ _ _)

theorem baseFamily_transitive (B : ℕ) :
    ∀ x ∈ baseFamily S B, ∀ y, y ∈ x → y ∈ baseFamily S B := by
  intro x hx y hy
  rcases mem_union.mp hx with hx|hx
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact False.elim (not_mem_atom _ _ hy)
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨k,hk,rfl⟩ := (mem_ordinal y i).mp hy
    exact mem_union_right _ (mem_image.mpr ⟨k,mem_range.mpr (by have := mem_range.mp hi; omega),rfl⟩)

theorem family_transitive (B j : ℕ) (hj : j ≤ B) :
    ∀ x ∈ P.family S B j, ∀ y, y ∈ x → y ∈ P.family S B j := by
  induction j with
  | zero => exact baseFamily_transitive S B
  | succ j ih =>
    have hp := ih (by omega)
    cases j with
    | zero =>
      exact stage_family_transitive P.init S atom 1 (P.family S B 0) hp
        (P.atom_mem_family S B 0) (P.ordinal_mem_family S B 0 1 hj)
    | succ k =>
      exact stage_family_transitive P.step (P.state S k) (P.code S k) (k+2)
        (P.family S B (k+1)) hp (P.code_mem_family S B k) (P.ordinal_mem_family S B (k+1) (k+2) hj)

theorem map_mem_baseFamily {S' : Structure R} (e : S.Iso S') (B : ℕ) {x : HF S.Carrier}
    (hx : x ∈ baseFamily S B) : map e.equiv x ∈ baseFamily S' B := by
  rcases mem_union.mp hx with hx|hx
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact mem_union_left _ (mem_image.mpr ⟨e.equiv a,mem_univ _,by simp⟩)
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_image.mpr ⟨i,hi,by simp⟩)

theorem map_mem_family {S' : Structure R} (e : S.Iso S') (B j : ℕ) {x : HF S.Carrier}
    (hx : x ∈ P.family S B j) : map e.equiv x ∈ P.family S' B j := by
  induction j generalizing x with
  | zero => exact map_mem_baseFamily S e B hx
  | succ j ih =>
    cases j with
    | zero =>
      rcases mem_union.mp hx with hx|hx
      · rcases mem_union.mp hx with hx|hx
        · exact mem_union_left _ (mem_union_left _ (ih hx))
        · exact mem_union_left _ (mem_union_right _
            (map_mem_pairFamily P.init e e.equiv atom atom (fun _ => map_atom _ _) hx))
      · exact mem_union_right _ (map_mem_classFamily P.init e e.equiv atom atom (fun _ => map_atom _ _) _ hx)
    | succ k =>
      rcases mem_union.mp hx with hx|hx
      · rcases mem_union.mp hx with hx|hx
        · exact mem_union_left _ (mem_union_left _ (ih hx))
        · exact mem_union_left _ (mem_union_right _
            (map_mem_pairFamily P.step (P.stateIso S e k) e.equiv (P.code S k) (P.code S' k)
              (P.map_code S e k) hx))
      · exact mem_union_right _ (map_mem_classFamily P.step (P.stateIso S e k) e.equiv
          (P.code S k) (P.code S' k) (P.map_code S e k) _ hx)

theorem baseFamily_card_le (B : ℕ) : (baseFamily S B).card ≤ Nat.card S.Carrier+B+1 := by
  calc
    (baseFamily S B).card ≤ (univ.image (atom : S.Carrier → HF S.Carrier)).card +
        ((range (B+1)).image (ordinal (A := S.Carrier))).card := card_union_le _ _
    _ ≤ univ.card + (range (B+1)).card := Nat.add_le_add (card_image_le) (card_image_le)
    _ = Nat.card S.Carrier+B+1 := by simp [Nat.card_eq_fintype_card,Nat.add_assoc]

theorem family_card_le (B j : ℕ) (hN : Nat.card S.Carrier ≤ B)
    (hsize : ∀ k < j, Nat.card (P.state S k).Carrier ≤ B) :
    (P.family S B j).card ≤ j*(3*B^2+4*B)+2*B+1 := by
  induction j with
  | zero =>
    have h := baseFamily_card_le S B
    simp only [Nat.zero_mul,Nat.zero_add]
    exact h.trans (by omega)
  | succ j ih =>
    have hprev := ih (fun k hk => hsize k (by omega))
    have hc := hsize j (by omega)
    have one_step {U V : Type} (I : Interpretation U V) (T : Structure U)
        (c : T.Carrier → HF S.Carrier) (tag : ℕ) (F : Finset (HF S.Carrier))
        (hp : Nat.card T.Carrier ≤ B) (hq : Nat.card (I.Vertex T) ≤ B) :
        (F ∪ pairFamily I T c ∪ classFamily I T c tag).card ≤ F.card+(3*B^2+4*B) := by
      have h1 := pairFamily_card_le I T c
      have h2 := classFamily_card_le I T c tag
      rw [← Nat.card_eq_fintype_card] at h1 h2
      have h1' : (pairFamily I T c).card ≤ 3*B^2 :=
        h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 2))
      have h2' : (classFamily I T c tag).card ≤ 4*B := h2.trans (Nat.mul_le_mul_left _ hq)
      have h3 := card_union_le (F ∪ pairFamily I T c) (classFamily I T c tag)
      have h4 := card_union_le F (pairFamily I T c)
      omega
    have hstep : (P.family S B (j+1)).card ≤ (P.family S B j).card+(3*B^2+4*B) := by
      cases j with
      | zero => exact one_step P.init S atom 1 _ hN hc
      | succ k => exact one_step P.step (P.state S k) (P.code S k) (k+2) _ (hsize k (by omega)) hc
    nlinarith

theorem trace_family (B j : ℕ) (hB : 2 ≤ B) (hj : j ≤ B)
    (hN : Nat.card S.Carrier ≤ B) (hsize : ∀ k < j, Nat.card (P.state S k).Carrier ≤ B) :
    (P.family S B j).card ≤ 9*B^3 ∧
    (∀ x ∈ P.family S B j, ∀ y, y ∈ x → y ∈ P.family S B j) ∧
    (∀ e : S.Iso S, ∀ x ∈ P.family S B j, map e.equiv x ∈ P.family S B j) := by
  refine ⟨?_,P.family_transitive S B j hj,fun e x hx => P.map_mem_family S e B j hx⟩
  have h := P.family_card_le S B j hN hsize
  have hj' := Nat.mul_le_mul_right (3*B^2+4*B) hj
  have hp := Nat.mul_le_mul_left (B^2) hB
  have hq := Nat.mul_le_mul_left B hB
  nlinarith

end Program

end

open Classical Finset

def Formula.scopedWidth {R : Type} : {n : ℕ} → Formula R n → ℕ
  | n, .falsum => n
  | n, .eq _ _ => n
  | n, .rel _ _ _ => n
  | _, .neg φ => φ.scopedWidth
  | _, .and φ ψ => max φ.scopedWidth ψ.scopedWidth
  | _, .ex φ => φ.scopedWidth
  | _, .hartig φ ψ => max φ.scopedWidth ψ.scopedWidth

theorem Formula.context_le_width {R : Type} {n : ℕ} (φ : Formula R n) : n ≤ φ.scopedWidth := by
  induction φ with
  | falsum => exact le_refl _
  | eq => exact le_refl _
  | rel => exact le_refl _
  | neg φ ih => exact ih
  | and φ ψ ihφ ihψ => exact ihφ.trans (Nat.le_max_left _ _)
  | ex φ ih => exact (Nat.le_succ _).trans ih
  | hartig φ ψ ihφ ihψ => exact (Nat.le_succ _).trans (ihφ.trans (Nat.le_max_left _ _))

private def guardedEquiv {X Y : Type} (e : X → Y) (he : Function.Injective e)
    (U : Y → Prop) (hU : ∀ y, U y ↔ ∃ x, e x = y) (p : X → Prop) (q : Y → Prop)
    (hq : ∀ x, q (e x) ↔ p x) : {x : X // p x} ≃ {y : Y // U y ∧ q y} :=
  Equiv.ofBijective (fun x => ⟨e x.val,⟨(hU _).mpr ⟨x.val,rfl⟩,(hq _).mpr x.property⟩⟩) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact he (congrArg Subtype.val hxy)
    · rintro ⟨y,hy,hqy⟩
      obtain ⟨x,rfl⟩ := (hU y).mp hy
      exact ⟨⟨x,(hq _).mp hqy⟩,rfl⟩)

private theorem count_comparison {X Y U V : Type} [Fintype X] [Fintype Y]
    (e : X ≃ U) (f : Y ≃ V) (B : ℕ) (hX : Nat.card X ≤ B) :
    (∃ k ≤ B, Nonempty (U ≃ Fin k) ∧ Nonempty (V ≃ Fin k)) ↔ Nat.card X = Nat.card Y := by
  constructor
  · rintro ⟨k,_,⟨g⟩,⟨h⟩⟩
    exact Nat.card_congr ((e.trans g).trans (f.trans h).symm)
  · intro h
    have hX' : Fintype.card X = Nat.card X := (Nat.card_eq_fintype_card).symm
    have hY' : Fintype.card Y = Nat.card X := by rw [← Nat.card_eq_fintype_card,← h]
    exact ⟨Nat.card X,hX,⟨e.symm.trans (Fintype.equivFinOfCardEq hX')⟩,
      ⟨f.symm.trans (Fintype.equivFinOfCardEq hY')⟩⟩

open Counting (UniformDefinable)

variable {ι R L : Type} {D : ι → Type}

variable (T : ι → Structure R) (S : ∀ i, Counting.Structure L (D i))

variable (e : ∀ i, (T i).Carrier → D i) (he : ∀ i, Function.Injective (e i))

variable (U : ∀ i, D i → Prop) (hU : ∀ i x, U i x ↔ ∃ a, e i a = x)

variable (rel : R → ∀ i, D i → D i → Prop)

variable (hrel : ∀ r i a b, rel r i (e i a) (e i b) ↔ (T i).rel r a b = true)

variable {m B : ℕ}

variable (hdU : UniformDefinable S m 1 (fun i v => U i (v 0)))

variable (hdR : ∀ r, UniformDefinable S m 2 (fun i v => rel r i (v 0) (v 1)))

variable (hB : ∀ i, Nat.card (T i).Carrier ≤ B)

include he hU hrel hdU hdR hB

theorem uniform_translate {n : ℕ} (φ : Formula R n) (hw : φ.scopedWidth < m) :
    ∃ Q : ∀ i, (Fin n → D i) → Prop, UniformDefinable S m n Q ∧
      ∀ i v, Q i (e i ∘ v) ↔ φ.eval (T i) v := by
  induction φ with
  | falsum => exact ⟨fun _ _ => False,UniformDefinable.falsum,fun _ _ => Iff.rfl⟩
  | eq x y =>
    exact ⟨fun _ v => v x = v y,UniformDefinable.equal x y,fun i _ => (he i).eq_iff⟩
  | rel r x y =>
    refine ⟨fun i v => rel r i (v x) (v y),?_,fun i v => hrel r i (v x) (v y)⟩
    simpa using (hdR r).reindex ![x,y]
  | neg φ ih =>
    obtain ⟨Q,hQ,hq⟩ := ih hw
    exact ⟨fun i v => ¬ Q i v,hQ.neg,fun i v => not_congr (hq i v)⟩
  | and φ ψ ihφ ihψ =>
    obtain ⟨Q,hQ,hq⟩ := ihφ (lt_of_le_of_lt (Nat.le_max_left _ _) hw)
    obtain ⟨P,hP,hp⟩ := ihψ (lt_of_le_of_lt (Nat.le_max_right _ _) hw)
    exact ⟨fun i v => Q i v ∧ P i v,hQ.and hP,fun i v => and_congr (hq i v) (hp i v)⟩
  | @ex n φ ih =>
    obtain ⟨Q,hQ,hq⟩ := ih hw
    have hu : UniformDefinable S m (n+1) (fun i v => U i (v 0)) := by
      simpa using hdU.reindex (fun _ : Fin 1 => (0 : Fin (n+1)))
    have hn : n < m := lt_of_le_of_lt ((Nat.le_succ _).trans φ.context_le_width) hw
    refine ⟨fun i v => ∃ x, U i x ∧ Q i (Fin.cons x v),(hu.and hQ).ex hn,?_⟩
    intro i v
    constructor
    · rintro ⟨x,hux,hqx⟩
      obtain ⟨a,rfl⟩ := (hU i x).mp hux
      exact ⟨a,(hq i (Fin.cons a v)).mp (by simpa only [Fin.comp_cons] using hqx)⟩
    · rintro ⟨a,ha⟩
      exact ⟨e i a,(hU i _).mpr ⟨a,rfl⟩,by simpa only [Fin.comp_cons] using (hq i (Fin.cons a v)).mpr ha⟩
  | @hartig n φ ψ ihφ ihψ =>
    obtain ⟨Q,hQ,hq⟩ := ihφ (lt_of_le_of_lt (Nat.le_max_left _ _) hw)
    obtain ⟨P,hP,hp⟩ := ihψ (lt_of_le_of_lt (Nat.le_max_right _ _) hw)
    have hu : UniformDefinable S m (n+1) (fun i v => U i (v 0)) := by
      simpa using hdU.reindex (fun _ : Fin 1 => (0 : Fin (n+1)))
    have hn : n < m := lt_of_le_of_lt ((Nat.le_succ _).trans
      (φ.context_le_width.trans (Nat.le_max_left _ _))) hw
    refine ⟨_,(hu.and hQ).bounded_hartig (hu.and hP) hn B,?_⟩
    intro i v
    have eqQ := guardedEquiv (e i) (he i) (U i) (hU i)
      (fun a => φ.eval (T i) (Fin.cons a v)) (fun x => Q i (Fin.cons x (e i ∘ v)))
      (fun a => by simpa only [Fin.comp_cons] using (hq i (Fin.cons a v)))
    have eqP := guardedEquiv (e i) (he i) (U i) (hU i)
      (fun a => ψ.eval (T i) (Fin.cons a v)) (fun x => P i (Fin.cons x (e i ∘ v)))
      (fun a => by simpa only [Fin.comp_cons] using (hp i (Fin.cons a v)))
    have hc : Nat.card {a : (T i).Carrier // φ.eval (T i) (Fin.cons a v)} ≤ B := by
      apply le_trans _ (hB i)
      rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    exact count_comparison eqQ eqP B hc

end CPTSeparation.Interpretations

namespace CPTSeparation.Reachability

open Classical

variable {X : Type*} (r : X → X → Prop)

def Link (a b : X) : Prop := a = b ∨ r a b ∨ r b a

def Reach : ℕ → X → X → Prop
  | 0, a, b => Link r a b
  | t+1, a, b => Reach t a b ∨ ∃ d, Reach t a d ∧ Link r d b

theorem mono {s t : ℕ} (h : s ≤ t) {a b : X} : Reach r s a b → Reach r t a b := by
  induction h with
  | refl => exact id
  | @step t h ih => exact fun hr => Or.inl (ih hr)

theorem left_extend {t : ℕ} {a b c : X} (hab : Link r a b) (hbc : Reach r t b c) :
    Reach r (t+1) a c := by
  induction t generalizing c with
  | zero => exact Or.inr ⟨b,hab,hbc⟩
  | succ t ih =>
    rcases hbc with hbc | ⟨d,hbd,hdc⟩
    · exact Or.inl (ih hbc)
    · exact Or.inr ⟨d,ih hbd,hdc⟩

theorem link_eqv {a b : X} (h : Link r a b) : Relation.EqvGen r a b := by
  rcases h with rfl | h | h
  · exact .refl a
  · exact .rel a b h
  · exact .symm b a (.rel b a h)

theorem reach_eqv {t : ℕ} {a b : X} (h : Reach r t a b) : Relation.EqvGen r a b := by
  induction t generalizing b with
  | zero => exact link_eqv r h
  | succ t ih =>
    rcases h with h | ⟨d,had,hdb⟩
    · exact ih h
    · exact .trans a d b (ih had) (link_eqv r hdb)

def graph : SimpleGraph X where
  Adj a b := (r a b ∨ r b a) ∧ a ≠ b
  symm := ⟨fun _ _ ⟨h,hn⟩ => ⟨h.symm,Ne.symm hn⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem eqv_walk {a b : X} (h : Relation.EqvGen r a b) : Nonempty ((graph r).Walk a b) := by
  induction h with
  | rel a b h =>
    by_cases hab : a = b
    · subst b; exact ⟨.nil⟩
    · exact ⟨.cons ⟨Or.inl h,hab⟩ .nil⟩
  | refl a => exact ⟨.nil⟩
  | symm a b _ ih => exact ih.map (fun p => p.reverse)
  | trans a b c _ _ ih ij =>
    obtain ⟨p⟩ := ih
    obtain ⟨q⟩ := ij
    exact ⟨p.append q⟩

theorem walk_reach {a b : X} (p : (graph r).Walk a b) : Reach r p.length a b := by
  induction p with
  | nil => exact Or.inl rfl
  | cons h p ih => exact left_extend r (Or.inr h.1) ih

theorem eqv_iff_bounded [Fintype X] (B : ℕ) (hB : Fintype.card X ≤ B) (a b : X) :
    Relation.EqvGen r a b ↔ Reach r B a b := by
  constructor
  · intro h
    obtain ⟨p⟩ := eqv_walk r h
    exact mono r (le_trans (Nat.le_of_lt (p.bypass_isPath.length_lt)) hB) (walk_reach r p.bypass)
  · exact reach_eqv r

end CPTSeparation.Reachability

namespace CPTSeparation.Counting

section

open Classical UniformDefinable

variable {ι R : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m : ℕ}

def PairReach (L : ∀ i, (Fin 4 → D i) → Prop) : ℕ → ∀ i, (Fin 4 → D i) → Prop
  | 0, i, v => L i v
  | t+1, i, v => PairReach L t i v ∨ ∃ x y,
      PairReach L t i ![v 0,v 1,x,y] ∧ L i ![x,y,v 2,v 3]

theorem uniform_pairReach (L : ∀ i, (Fin 4 → D i) → Prop)
    (hL : UniformDefinable S m 4 L) (hm : 6 ≤ m) (t : ℕ) :
    UniformDefinable S m 4 (PairReach L t) := by
  induction t with
  | zero => exact hL
  | succ t ih =>
    have ha := ih.reindex (![2,3,1,0] : Fin 4 → Fin 6)
    have hb := hL.reindex (![1,0,4,5] : Fin 4 → Fin 6)
    apply ih.or
    apply (((ha.and hb).ex (by omega)).ex (by omega)).congr
    intro i v
    apply exists_congr
    intro x
    apply exists_congr
    intro y
    have h₁ : Fin.cons y (Fin.cons x v) ∘ ![2,3,1,0] = ![v 0,v 1,x,y] := by ext k; fin_cases k <;> rfl
    have h₂ : Fin.cons y (Fin.cons x v) ∘ ![1,0,4,5] = ![x,y,v 2,v 3] := by ext k; fin_cases k <;> rfl
    rw [h₁,h₂]

end

open Classical

variable {ι D₀ : Type*} (X : Type*) [finiteX : Fintype X] (r : X → X → Prop)

variable (a b : X → D₀) (hinj : Function.Injective (fun x => (a x,b x)))

variable (L : (Fin 4 → D₀) → Prop)

variable (hL : ∀ v, L v ↔ ∃ p q, v 0 = a p ∧ v 1 = b p ∧
  v 2 = a q ∧ v 3 = b q ∧ Reachability.Link r p q)

include hinj hL

omit D₀ X r a b hinj L hL in
theorem pairReach_lift.{uDecl2, uDecl3}
    {D₀ : Type uDecl2}
    (X : Type uDecl3)
    [Fintype X]
    (r : X → X → Prop)
    (a : X → D₀)
    (b : X → D₀)
    (hinj : Function.Injective fun x => (a x, b x))
    (L : (Fin 4 → D₀) → Prop)
    (hL : ∀ (v : Fin 4 → D₀), L v ↔ ∃ p q, v 0 = a p ∧ v 1 = b p ∧ v 2 = a q ∧ v 3 = b q ∧ Reachability.Link r p q) (t : ℕ) (v : Fin 4 → D₀) :
    PairReach (fun _ : Unit => L) t () v ↔ ∃ p q, v 0 = a p ∧ v 1 = b p ∧
      v 2 = a q ∧ v 3 = b q ∧ Reachability.Reach r t p q := by
  induction t generalizing v with
  | zero => exact hL v
  | succ t ih =>
    change (_ ∨ ∃ x y, _ ∧ _) ↔ _
    constructor
    · rintro (hv|⟨x,y,hv,hw⟩)
      · obtain ⟨p,q,hp₁,hp₂,hq₁,hq₂,hpq⟩ := (ih v).mp hv
        exact ⟨p,q,hp₁,hp₂,hq₁,hq₂,Or.inl hpq⟩
      · obtain ⟨p,c,hp₁,hp₂,hc₁,hc₂,hpc⟩ := (ih _).mp hv
        obtain ⟨c',q,hc'₁,hc'₂,hq₁,hq₂,hcq⟩ := (hL _).mp hw
        have hc : c = c' := hinj (Prod.ext (hc₁.symm.trans hc'₁) (hc₂.symm.trans hc'₂))
        subst c'
        exact ⟨p,q,hp₁,hp₂,hq₁,hq₂,Or.inr ⟨c,hpc,hcq⟩⟩
    · rintro ⟨p,q,hp₁,hp₂,hq₁,hq₂,hpq⟩
      rcases hpq with hpq | ⟨c,hpc,hcq⟩
      · exact Or.inl ((ih v).mpr ⟨p,q,hp₁,hp₂,hq₁,hq₂,hpq⟩)
      · exact Or.inr ⟨a c,b c,(ih _).mpr ⟨p,c,hp₁,hp₂,rfl,rfl,hpc⟩,
          (hL _).mpr ⟨c,q,rfl,rfl,hq₁,hq₂,hcq⟩⟩

theorem pairReach_eqv (B : ℕ) (hB : Fintype.card X ≤ B) (v : Fin 4 → D₀) :
    PairReach (fun _ : Unit => L) B () v ↔ ∃ p q, v 0 = a p ∧ v 1 = b p ∧
      v 2 = a q ∧ v 3 = b q ∧ Relation.EqvGen r p q := by
  rw [pairReach_lift X r a b hinj L hL]
  simp only [← Reachability.eqv_iff_bounded r B hB]

end CPTSeparation.Counting

namespace CPTSeparation.Interpretations

section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i)) (he : ∀ i, Function.Injective (e i))

variable {m B : ℕ} (I : Interpretation R T)

def EncodedDomain : ∀ i, (Fin 2 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2

def EncodedLink : ∀ i, (Fin 4 → Domain (d i)) → Prop := fun i v =>
  ∃ p q : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2 ∧
    v 2 = e i q.val.1 ∧ v 3 = e i q.val.2 ∧ Reachability.Link (I.link (S i)) p q

def EncodedClass : ∀ i, (Fin 4 → Domain (d i)) → Prop := fun i v =>
  ∃ p q : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2 ∧
    v 2 = e i q.val.1 ∧ v 3 = e i q.val.2 ∧ Quotient.mk (I.classSetoid (S i)) p = Quotient.mk _ q

variable (U : ∀ i, Domain (d i) → Prop) (hU : ∀ i x, U i x ↔ ∃ a, e i a = x)

variable (hdu : UniformDefinable C m 1 (fun i v => U i (v 0)))

variable (δ : ∀ i, (Fin 2 → Domain (d i)) → Prop) (hdδ : UniformDefinable C m 2 δ)

variable (hδ : ∀ i v, δ i (e i ∘ v) ↔ I.domain.eval (S i) v)

include hU hdu hdδ hδ

theorem uniform_domain : UniformDefinable C m 2 (EncodedDomain S e I) := by
  have h₁ : UniformDefinable C m 2 (fun i v => U i (v 0)) := by simpa using hdu.reindex (![0] : Fin 1 → Fin 2)
  have h₂ : UniformDefinable C m 2 (fun i v => U i (v 1)) := by simpa using hdu.reindex (![1] : Fin 1 → Fin 2)
  apply (h₁.and (h₂.and hdδ)).congr
  intro i v
  constructor
  · rintro ⟨h₁,h₂,hv⟩
    obtain ⟨a,ha⟩ := (hU i (v 0)).mp h₁
    obtain ⟨b,hb⟩ := (hU i (v 1)).mp h₂
    have hvv : e i ∘ ![a,b] = v := by ext k; fin_cases k <;> simp [ha,hb]
    exact ⟨⟨(a,b),(hδ i _).mp (by rw [hvv]; exact hv)⟩,ha.symm,hb.symm⟩
  · rintro ⟨p,h₁,h₂⟩
    have hvv : e i ∘ ![p.val.1,p.val.2] = v := by ext k; fin_cases k <;> simp [h₁,h₂]
    refine ⟨(hU i _).mpr ⟨p.val.1,h₁.symm⟩,(hU i _).mpr ⟨p.val.2,h₂.symm⟩,?_⟩
    rw [← hvv]
    exact (hδ i _).mpr p.property

omit hU hdu hdδ hδ

variable (hdom : UniformDefinable C m 2 (EncodedDomain S e I))

variable (η : ∀ i, (Fin 4 → Domain (d i)) → Prop) (hdη : UniformDefinable C m 4 η)

variable (hη : ∀ i v, η i (e i ∘ v) ↔ I.identify.eval (S i) v)

include he hdom hdη hη

theorem uniform_link : UniformDefinable C m 4 (EncodedLink S e I) := by
  have h₁ := hdom.reindex (![0,1] : Fin 2 → Fin 4)
  have h₂ := hdom.reindex (![2,3] : Fin 2 → Fin 4)
  have heq : UniformDefinable C m 4 (fun _ v => v 0 = v 2 ∧ v 1 = v 3) :=
    (UniformDefinable.equal 0 2).and (UniformDefinable.equal 1 3)
  have ht := hdη.reindex (![2,3,0,1] : Fin 4 → Fin 4)
  apply (h₁.and (h₂.and (heq.or (hdη.or ht)))).congr
  intro i v
  constructor
  · rintro ⟨⟨p,hp₁,hp₂⟩,⟨q,hq₁,hq₂⟩,hr⟩
    refine ⟨p,q,hp₁,hp₂,hq₁,hq₂,?_⟩
    rcases hr with ⟨he₁,he₂⟩ | hr | hr
    · exact Or.inl (Subtype.ext (Prod.ext (he i (hp₁.symm.trans (he₁.trans hq₁)))
        (he i (hp₂.symm.trans (he₂.trans hq₂)))))
    · have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = v := by
        funext k; fin_cases k
        · exact hp₁.symm
        · exact hp₂.symm
        · exact hq₁.symm
        · exact hq₂.symm
      exact Or.inr (Or.inl ((hη i _).mp (by rw [hvv]; exact hr)))
    · have hvv : e i ∘ ![q.val.1,q.val.2,p.val.1,p.val.2] = v ∘ ![2,3,0,1] := by
        funext k; fin_cases k
        · exact hq₁.symm
        · exact hq₂.symm
        · exact hp₁.symm
        · exact hp₂.symm
      exact Or.inr (Or.inr ((hη i _).mp (by rw [hvv]; exact hr)))
  · rintro ⟨p,q,hp₁,hp₂,hq₁,hq₂,hr⟩
    refine ⟨⟨p,hp₁,hp₂⟩,⟨q,hq₁,hq₂⟩,?_⟩
    rcases hr with rfl | hr | hr
    · exact Or.inl ⟨hp₁.trans hq₁.symm,hp₂.trans hq₂.symm⟩
    · have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = v := by
        funext k; fin_cases k
        · exact hp₁.symm
        · exact hp₂.symm
        · exact hq₁.symm
        · exact hq₂.symm
      exact Or.inr (Or.inl (by rw [← hvv]; exact (hη i _).mpr hr))
    · have hvv : e i ∘ ![q.val.1,q.val.2,p.val.1,p.val.2] = v ∘ ![2,3,0,1] := by
        funext k; fin_cases k
        · exact hq₁.symm
        · exact hq₂.symm
        · exact hp₁.symm
        · exact hp₂.symm
      exact Or.inr (Or.inr (by rw [← hvv]; exact (hη i _).mpr hr))

omit hdom hdη hη

variable (hlink : UniformDefinable C m 4 (EncodedLink S e I))

include hlink

theorem uniform_class (hm : 6 ≤ m) (hB : ∀ i, Nat.card (S i).Carrier ≤ B) :
    UniformDefinable C m 4 (EncodedClass S e I) := by
  apply (Counting.uniform_pairReach C (EncodedLink S e I) hlink hm (B^2)).congr
  intro i v
  have hinj : Function.Injective (fun p : I.Domain (S i) => (e i p.val.1,e i p.val.2)) := by
    intro p q hpq
    exact Subtype.ext (Prod.ext (he i (congrArg Prod.fst hpq)) (he i (congrArg Prod.snd hpq)))
  have hc : Fintype.card (I.Domain (S i)) ≤ B^2 := by
    apply le_trans (Fintype.card_subtype_le _)
    rw [Fintype.card_prod,← Nat.card_eq_fintype_card]
    simpa only [pow_two] using Nat.mul_self_le_mul_self (hB i)
  have h := Counting.pairReach_eqv (I.Domain (S i)) (I.link (S i))
    (fun p => e i p.val.1) (fun p => e i p.val.2) hinj (EncodedLink S e I i)
    (fun _ => Iff.rfl) (B^2) hc v
  have heq : PairReach (EncodedLink S e I) (B^2) i v =
      PairReach (fun _ : Unit => EncodedLink S e I i) (B^2) () v := by
    clear h
    generalize B^2 = t
    induction t generalizing v with
    | zero => rfl
    | succ t ih => simp only [PairReach,ih]
  rw [heq,h]
  unfold EncodedClass
  apply exists_congr
  intro p
  apply exists_congr
  intro q
  refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
    and_congr_right (fun _ => ?_))))
  change (I.classSetoid (S i)).r p q ↔ _
  exact Quotient.eq.symm

end

section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i)) (he : ∀ i, Function.Injective (e i))

variable {m : ℕ} (I : Interpretation R T)

def EncodedPayload : ∀ i, (Fin 3 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 1 = e i p.val.1 ∧ v 2 = e i p.val.2 ∧
    (v 0).val = payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)

def EncodedRep (j : ℕ) : ∀ i, (Fin 3 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 1 = e i p.val.1 ∧ v 2 = e i p.val.2 ∧
    (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j (Quotient.mk _ p)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

variable (hdom : UniformDefinable C m 2 (EncodedDomain S e I))

variable (hclass : UniformDefinable C m 4 (EncodedClass S e I))

variable (hpairs : ∀ i (p : I.Domain (S i)), pair (e i p.val.1).val (e i p.val.2).val ∈ d i)

include he hd hmem hset hm hdom hclass hpairs

theorem uniform_payload : UniformDefinable C m 3 (EncodedPayload S e I) := by
  have hc := hclass.reindex (![4,5,1,0] : Fin 4 → Fin 6)
  have hp := (HFCoding.uniform_pair C hmem hset hm hd).reindex (![2,1,0] : Fin 3 → Fin 6)
  have hr := ((hc.and hp).ex (by omega)).ex (by omega)
  have hmem' := hmem.reindex (![0,1] : Fin 2 → Fin 4)
  have hall := (hmem'.iff hr).all (by omega)
  have hs := hset.reindex (![0] : Fin 1 → Fin 3)
  have hdo := hdom.reindex (![1,2] : Fin 2 → Fin 3)
  apply (hs.and (hdo.and hall)).congr
  intro i v
  change (isSet (v 0).val = true ∧ EncodedDomain S e I i ![v 1,v 2] ∧
    ∀ z : Domain (d i), z.val ∈ (v 0).val ↔ ∃ b₁ b₂ : Domain (d i),
      EncodedClass S e I i ![v 1,v 2,b₁,b₂] ∧ z.val = pair b₁.val b₂.val) ↔ _
  constructor
  · rintro ⟨hs,⟨p,hp₁,hp₂⟩,h⟩
    refine ⟨p,hp₁,hp₂,?_⟩
    apply ext_sets hs (isSet_ofFinset _)
    intro z
    change z ∈ (v 0).val ↔ z ∈ payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)
    rw [mem_payload]
    constructor
    · intro hz
      obtain ⟨b₁,b₂,⟨p',q,hp'₁,hp'₂,hq₁,hq₂,hpq⟩,hzq⟩ :=
        (h ⟨z,hd i _ (v 0).property _ hz⟩).mp hz
      have hpp : p = p' := Subtype.ext (Prod.ext (he i (hp₁.symm.trans hp'₁)) (he i (hp₂.symm.trans hp'₂)))
      subst p'
      change b₁ = e i q.val.1 at hq₁
      change b₂ = e i q.val.2 at hq₂
      exact ⟨q,hpq.symm,by simpa only [hq₁,hq₂,Function.comp_apply] using hzq⟩
    · rintro ⟨q,hqp,rfl⟩
      have hz := hpairs i q
      exact (h ⟨_,hz⟩).mpr ⟨e i q.val.1,e i q.val.2,
        ⟨p,q,hp₁,hp₂,rfl,rfl,hqp.symm⟩,rfl⟩
  · rintro ⟨p,hp₁,hp₂,hv⟩
    refine ⟨by rw [hv]; exact isSet_ofFinset _,⟨p,hp₁,hp₂⟩,?_⟩
    intro z
    rw [hv,mem_payload]
    constructor
    · rintro ⟨q,hqp,hzq⟩
      exact ⟨e i q.val.1,e i q.val.2,⟨p,q,hp₁,hp₂,rfl,rfl,hqp.symm⟩,hzq⟩
    · rintro ⟨b₁,b₂,⟨p',q,hp'₁,hp'₂,hq₁,hq₂,hpq⟩,hzq⟩
      have hpp : p = p' := Subtype.ext (Prod.ext (he i (hp₁.symm.trans hp'₁)) (he i (hp₂.symm.trans hp'₂)))
      subst p'
      change b₁ = e i q.val.1 at hq₁
      change b₂ = e i q.val.2 at hq₂
      exact ⟨q,hpq.symm,by simpa only [hq₁,hq₂,Function.comp_apply] using hzq⟩

end

section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i))

variable {m : ℕ} (I : Interpretation R T)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (hpayload : UniformDefinable C m 3 (EncodedPayload S e I))

include hd hmem hset hm hpure hpayload

theorem uniform_rep (j : ℕ) : UniformDefinable C m 3 (EncodedRep S e I j) := by
  have ho := (HFCoding.uniform_ordinal C hmem hset hm hd hpure j).reindex (![1] : Fin 1 → Fin 5)
  have hs := hpayload.reindex (![0,3,4] : Fin 3 → Fin 5)
  have hp := (HFCoding.uniform_pair C hmem hset hm hd).reindex (![2,1,0] : Fin 3 → Fin 5)
  apply (((ho.and (hs.and hp)).ex (by omega)).ex (by omega)).congr
  intro i v
  change (∃ o S' : Domain (d i), o.val = ordinal j ∧ EncodedPayload S e I i ![S',v 1,v 2] ∧
    (v 0).val = pair o.val S'.val) ↔ _
  constructor
  · rintro ⟨o,S',ho,⟨p,hp₁,hp₂,hS⟩,hx⟩
    change S'.val = payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p) at hS
    exact ⟨p,hp₁,hp₂,by simpa only [vertexCode,ho,hS] using hx⟩
  · rintro ⟨p,hp₁,hp₂,hx⟩
    let pl := payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)
    have hp : pl ∈ d i := by
      have hdbl : double (ordinal j) pl ∈ d i := hd i _ (v 0).property _ (by rw [hx]; simp [vertexCode,pair,pl])
      exact hd i _ hdbl _ (by simp)
    exact ⟨⟨ordinal j,hpure i j⟩,⟨pl,hp⟩,rfl,⟨p,hp₁,hp₂,rfl⟩,hx⟩

omit hd hmem hset hpure hpayload

variable (j : ℕ) (hrep : UniformDefinable C m 3 (EncodedRep S e I j))

include hrep

def EncodedUniverse : ∀ i, (Fin 1 → Domain (d i)) → Prop := fun i v =>
  ∃ x : I.Vertex (S i), (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j x

theorem uniform_universe : UniformDefinable C m 1 (EncodedUniverse S e I j) := by
  have hr := hrep.reindex (![2,1,0] : Fin 3 → Fin 3)
  apply ((hr.ex (by omega)).ex (by omega)).congr
  intro i v
  change (∃ a b, EncodedRep S e I j i ![v 0,a,b]) ↔ _
  constructor
  · rintro ⟨a,b,p,_,_,hx⟩
    exact ⟨Quotient.mk _ p,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨p,rfl⟩ := Quotient.exists_rep x
    exact ⟨e i p.val.1,e i p.val.2,p,rfl,rfl,hx⟩

def EncodedStateRelation (r : T) : ∀ i, (Fin 2 → Domain (d i)) → Prop := fun i v =>
  ∃ x y : I.Vertex (S i), (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j x ∧
    (v 1).val = vertexCode I (S i) (Subtype.val ∘ e i) j y ∧ (I.apply (S i)).rel r x y = true

variable (ρ : ∀ i, (Fin 4 → Domain (d i)) → Prop)

variable (hdρ : UniformDefinable C m 4 ρ)

include hdρ

theorem uniform_stateRelation (r : T)
    (hρ : ∀ i v, ρ i (e i ∘ v) ↔ (I.relation r).eval (S i) v) :
    UniformDefinable C m 2 (EncodedStateRelation S e I j r) := by
  have hx := hrep.reindex (![4,3,2] : Fin 3 → Fin 6)
  have hy := hrep.reindex (![5,1,0] : Fin 3 → Fin 6)
  have hr := hdρ.reindex (![3,2,1,0] : Fin 4 → Fin 6)
  apply (((((hx.and (hy.and hr)).ex (by omega)).ex (by omega)).ex (by omega)).ex (by omega)).congr
  intro i v
  have hvec (a₁ a₂ b₁ b₂ : Domain (d i)) :
      Fin.cons b₂ (Fin.cons b₁ (Fin.cons a₂ (Fin.cons a₁ v))) ∘ ![3,2,1,0] = ![a₁,a₂,b₁,b₂] := by
    funext k; fin_cases k <;> rfl
  simp only [hvec]
  change (∃ a₁ a₂ b₁ b₂, EncodedRep S e I j i ![v 0,a₁,a₂] ∧
    EncodedRep S e I j i ![v 1,b₁,b₂] ∧ ρ i ![a₁,a₂,b₁,b₂]) ↔ _
  constructor
  · rintro ⟨a₁,a₂,b₁,b₂,⟨p,hp₁,hp₂,hx⟩,⟨q,hq₁,hq₂,hy⟩,hr⟩
    refine ⟨Quotient.mk _ p,Quotient.mk _ q,hx,hy,?_⟩
    simp only [Interpretation.apply,decide_eq_true_eq]
    refine ⟨p,q,rfl,rfl,?_⟩
    have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = ![a₁,a₂,b₁,b₂] := by
      funext k; fin_cases k
      · exact hp₁.symm
      · exact hp₂.symm
      · exact hq₁.symm
      · exact hq₂.symm
    exact (hρ i _).mp (by rw [hvv]; exact hr)
  · rintro ⟨x,y,hx,hy,hxy⟩
    simp only [Interpretation.apply,decide_eq_true_eq] at hxy
    obtain ⟨p,q,hp,hq,hr⟩ := hxy
    refine ⟨e i p.val.1,e i p.val.2,e i q.val.1,e i q.val.2,
      ⟨p,rfl,rfl,by change (v 0).val = _; rw [hp]; exact hx⟩,
      ⟨q,rfl,rfl,by change (v 1).val = _; rw [hq]; exact hy⟩,?_⟩
    have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] =
        ![e i p.val.1,e i p.val.2,e i q.val.1,e i q.val.2] := by funext k; fin_cases k <;> rfl
    rw [← hvv]
    exact (hρ i _).mpr hr

end

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {D : ι → Type}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (D i))

variable (e : ∀ i, (S i).Carrier → D i) {m B : ℕ}

structure StateDefinable (m : ℕ) : Prop where
  domainDef : UniformDefinable C m 1 (fun i v => ∃ a, e i a = v 0)
  relations : ∀ r, UniformDefinable C m 2 (fun i v => ∃ a b,
    e i a = v 0 ∧ e i b = v 1 ∧ (S i).rel r a b = true)

theorem StateDefinable.translate (h : StateDefinable S C e m) (he : ∀ i, Function.Injective (e i))
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B) {k : ℕ} (φ : Formula R k) (hw : φ.scopedWidth < m) :
    ∃ Q : ∀ i, (Fin k → D i) → Prop, UniformDefinable C m k Q ∧
      ∀ i v, Q i (e i ∘ v) ↔ φ.eval (S i) v := by
  apply uniform_translate S C e he (fun i x => ∃ a, e i a = x) (fun _ _ => Iff.rfl)
    (fun r i x y => ∃ a b, e i a = x ∧ e i b = y ∧ (S i).rel r a b = true)
    _ h.domainDef h.relations hB φ hw
  intro r i a b
  constructor
  · rintro ⟨a',b',ha,hb,hr⟩
    simpa only [he i ha,he i hb] using hr
  · exact fun hr => ⟨a,b,rfl,rfl,hr⟩

variable {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (H : ∀ i, Counting.Structure L (Domain (d i)))

variable (f : ∀ i, (S i).Carrier → Domain (d i)) (hf : ∀ i, Function.Injective (f i))

variable (I : Interpretation R T) (j : ℕ)

variable (hc : ∀ i x, vertexCode I (S i) (Subtype.val ∘ f i) j x ∈ d i)

def nextCode (i : ι) (x : (I.apply (S i)).Carrier) : Domain (d i) :=
  ⟨vertexCode I (S i) (Subtype.val ∘ f i) j x,hc i x⟩

include hf in
theorem nextCode_injective (i : ι) : Function.Injective (nextCode S f I j hc i) := by
  intro x y hxy
  exact vertexCode_injective I (S i) (Subtype.val ∘ f i) (Subtype.val_injective.comp (hf i)) j
    (congrArg Subtype.val hxy)

include hf

theorem StateDefinable.apply (h : StateDefinable S H f m)
    (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
    (hmem : UniformDefinable H m 2 (fun _ v => (v 0).val ∈ (v 1).val))
    (hset : UniformDefinable H m 1 (fun _ v => isSet (v 0).val = true))
    (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := A i) k ∈ d i)
    (hpairs : ∀ i (p : I.Domain (S i)), pair (f i p.val.1).val (f i p.val.2).val ∈ d i)
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B)
    (hwδ : I.domain.scopedWidth < m) (hwη : I.identify.scopedWidth < m)
    (hwρ : ∀ r, (I.relation r).scopedWidth < m) :
    StateDefinable (fun i => I.apply (S i)) H (nextCode S f I j hc) m := by
  obtain ⟨δ,hdδ,hδ⟩ := h.translate S H f hf hB I.domain hwδ
  obtain ⟨η,hdη,hη⟩ := h.translate S H f hf hB I.identify hwη
  have hdom := uniform_domain S H f I (fun i x => ∃ a, f i a = x)
    (fun _ _ => Iff.rfl) h.domainDef δ hdδ hδ
  have hlink := uniform_link S H f hf I hdom η hdη hη
  have hclass := uniform_class S H f hf I hlink hm hB
  have hpay := uniform_payload S H f hf I hd hmem hset hm hdom hclass hpairs
  have hrep := uniform_rep S H f I hd hmem hset hm hpure hpay j
  constructor
  · apply (uniform_universe S H f I hm j hrep).congr
    intro i v
    exact exists_congr (fun x => ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩)
  · intro r
    obtain ⟨ρ,hdρ,hρ⟩ := h.translate S H f hf hB (I.relation r) (hwρ r)
    apply (uniform_stateRelation S H f I hm j hrep ρ hdρ r hρ).congr
    intro i v
    apply exists_congr
    intro x
    apply exists_congr
    intro y
    exact and_congr (⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩)
      (and_congr (⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩) Iff.rfl)

end CPTSeparation.Interpretations

namespace CPTSeparation.Interpretations.Program

open Classical Counting HFCoding Hereditary Finset

variable {ι R L : Type} (P : Program R)

theorem exists_width : ∃ m : ℕ, 6 ≤ m ∧
    P.init.domain.scopedWidth < m ∧ P.init.identify.scopedWidth < m ∧
    (∀ r, (P.init.relation r).scopedWidth < m) ∧
    P.step.domain.scopedWidth < m ∧ P.step.identify.scopedWidth < m ∧
    (∀ r, (P.step.relation r).scopedWidth < m) ∧
    P.halt.scopedWidth < m ∧ P.output.scopedWidth < m := by
  let := P.stateFinite
  let b : ℕ := univ.sup (fun r => max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth)
  let m := 7 + P.init.domain.scopedWidth + P.init.identify.scopedWidth + b +
    P.step.domain.scopedWidth + P.step.identify.scopedWidth + P.halt.scopedWidth + P.output.scopedWidth
  have hb (r) : max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth ≤ b :=
    le_sup (f := fun r => max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth) (mem_univ r)
  refine ⟨m,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro r; have h := hb r; dsimp [m]; omega) | (dsimp [m]; omega)

variable (S : ι → Structure R) {d : ∀ i, Set (HF (S i).Carrier)}

variable (C : ∀ i, Counting.Structure L (Domain (d i)))

variable {B K m : ℕ}

theorem family_mono_le (A : Structure R) (B : ℕ) {j k : ℕ} (h : j ≤ k) :
    P.family A B j ⊆ P.family A B k := by
  induction h with
  | refl => exact Subset.rfl
  | @step k h ih => exact ih.trans (P.family_mono A B k)

variable (hfamily : ∀ i x, x ∈ P.family (S i) B K → x ∈ d i)

include hfamily in
theorem code_mem_domain {j : ℕ} (hj : j < K) (i : ι) (a : (P.state (S i) j).Carrier) :
    P.code (S i) j a ∈ d i :=
  hfamily i _ (P.family_mono_le (S i) B (by omega) (P.code_mem_family (S i) B j a))

def stateCode {j : ℕ} (hj : j < K) (i : ι) (a : (P.state (S i) j).Carrier) : Domain (d i) :=
  ⟨P.code (S i) j a,P.code_mem_domain S hfamily hj i a⟩

theorem stateCode_injective {j : ℕ} (hj : j < K) (i : ι) :
    Function.Injective (P.stateCode S hfamily hj i) := by
  intro a b h
  exact P.code_injective (S i) j (congrArg Subtype.val h)

def inputCode (i : ι) (a : (S i).Carrier) : Domain (d i) :=
  ⟨atom a,hfamily i _ (P.atom_mem_family (S i) B K a)⟩

theorem inputCode_injective (i : ι) : Function.Injective (P.inputCode S hfamily i) := by
  intro a b h
  exact atom_injective (congrArg Subtype.val h)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := (S i).Carrier) k ∈ d i)

variable (hN : ∀ i, Nat.card (S i).Carrier ≤ B)

variable (hsize : ∀ i j, j < K → Nat.card (P.state (S i) j).Carrier ≤ B)

variable (wiδ : P.init.domain.scopedWidth < m) (wiη : P.init.identify.scopedWidth < m)

variable (wiρ : ∀ r, (P.init.relation r).scopedWidth < m)

variable (wsδ : P.step.domain.scopedWidth < m) (wsη : P.step.identify.scopedWidth < m)

variable (wsρ : ∀ r, (P.step.relation r).scopedWidth < m)

variable (hinput : StateDefinable S C (P.inputCode S hfamily) m)

include hd hmem hset hm hpure hN hsize wiδ wiη wiρ wsδ wsη wsρ hinput

theorem state_definable {j : ℕ} (hj : j < K) :
    StateDefinable (fun i => P.state (S i) j) C (P.stateCode S hfamily hj) m := by
  induction j with
  | zero =>
    have hpairs (i) (p : P.init.Domain (S i)) :
        pair (P.inputCode S hfamily i p.val.1).val (P.inputCode S hfamily i p.val.2).val ∈ d i := by
      apply hfamily i
      apply P.family_mono_le (S i) B (show 1 ≤ K by omega)
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨p,mem_univ _,by simp [wrappers,inputCode]⟩
    have hc (i) (x : P.init.Vertex (S i)) :
        vertexCode P.init (S i) (Subtype.val ∘ P.inputCode S hfamily i) 1 x ∈ d i :=
      P.code_mem_domain S hfamily hj i x
    exact hinput.apply S C (P.inputCode S hfamily) (P.inputCode_injective S hfamily) P.init 1 hc
      hd hmem hset hm hpure hpairs hN wiδ wiη wiρ
  | succ j ih =>
    have hj' : j < K := by omega
    have hpairs (i) (p : P.step.Domain (P.state (S i) j)) :
        pair (P.stateCode S hfamily hj' i p.val.1).val (P.stateCode S hfamily hj' i p.val.2).val ∈ d i := by
      apply hfamily i
      apply P.family_mono_le (S i) B (show j+2 ≤ K by omega)
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨p,mem_univ _,by simp [wrappers,stateCode]⟩
    have hc (i) (x : P.step.Vertex (P.state (S i) j)) :
        vertexCode P.step (P.state (S i) j) (Subtype.val ∘ P.stateCode S hfamily hj' i) (j+2) x ∈ d i :=
      P.code_mem_domain S hfamily hj i x
    exact (ih hj').apply (fun i => P.state (S i) j) C (P.stateCode S hfamily hj')
      (P.stateCode_injective S hfamily hj') P.step (j+2) hc hd hmem hset hm hpure hpairs
      (fun i => hsize i j hj') wsδ wsη wsρ

end CPTSeparation.Interpretations.Program

namespace CPTSeparation.Interpretations

open Classical Counting

variable {ι R L : Type} {D : ι → Type}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (D i))

variable (e : ∀ i, (S i).Carrier → D i) {m B : ℕ}

theorem StateDefinable.sentence (h : StateDefinable S C e m) (he : ∀ i, Function.Injective (e i))
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B) (ψ : Formula R 0) (hw : ψ.scopedWidth < m) :
    ∃ φ : Counting.Formula L (Fin m), φ.free = ∅ ∧
      ∀ i v, φ.eval (C i) v ↔ ψ.holds (S i) := by
  obtain ⟨Q,hQ,hψ⟩ := h.translate S C e he hB ψ hw
  obtain ⟨φ,hφ,hφQ⟩ := hQ Fin.elim0
  refine ⟨φ,?_,?_⟩
  · apply Finset.subset_empty.mp
    simpa only [Finset.univ_eq_empty,Finset.image_empty] using hφ
  · intro i v
    have hv : v ∘ (Fin.elim0 : Fin 0 → Fin m) = e i ∘ Fin.elim0 := by funext k; exact k.elim0
    exact (hφQ i v).trans (by rw [hv]; exact hψ i Fin.elim0)

namespace Program

variable {R : Type} (P : Program R)

theorem haltsAt_unique (S : Structure R) {j k : ℕ} (hj : P.haltsAt S j) (hk : P.haltsAt S k) : j = k := by
  rcases lt_trichotomy j k with h|h|h
  · exact False.elim (hk.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 k h hk.1)

theorem accepts_iff_of_haltsAt (S : Structure R) {j : ℕ} (hj : P.haltsAt S j) :
    P.accepts S ↔ P.output.holds (P.state S j) := by
  constructor
  · rintro ⟨k,hk,hout⟩
    rwa [P.haltsAt_unique S hk hj] at hout
  · exact fun hout => ⟨j,hj,hout⟩

theorem synchronize (S T : Structure R) {j k : ℕ}
    (hj : P.haltsAt S j) (hk : P.haltsAt T k)
    (hhalt : ∀ l ≤ min j k, P.halt.holds (P.state S l) ↔ P.halt.holds (P.state T l))
    (hout : ∀ l ≤ min j k, P.output.holds (P.state S l) ↔ P.output.holds (P.state T l)) :
    j = k ∧ (P.accepts S ↔ P.accepts T) := by
  have heq : j = k := by
    rcases le_total j k with h|h
    · have hh := (hhalt j (by omega)).mp hj.1
      have hkj : k ≤ j := by by_contra h'; exact hk.2 j (by omega) hh
      omega
    · have hh := (hhalt k (by omega)).mpr hk.1
      have hjk : j ≤ k := by by_contra h'; exact hj.2 k (by omega) hh
      omega
  refine ⟨heq,?_⟩
  rw [P.accepts_iff_of_haltsAt S hj,P.accepts_iff_of_haltsAt T hk,← heq]
  exact hout j (by omega)

end Program

end CPTSeparation.Interpretations

end

end OAI
