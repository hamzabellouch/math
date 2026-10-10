import OAI.ModelTheory.Choiceless.Forms

namespace OAI

noncomputable section

namespace CPTSeparation.Interpretations

structure Structure (R : Type) where
  Carrier : Type
  finite : Fintype Carrier
  rel : R → Carrier → Carrier → Bool

attribute [instance] Structure.finite

inductive Formula (R : Type) : ℕ → Type
  | falsum {n} : Formula R n
  | eq {n} (x y : Fin n) : Formula R n
  | rel {n} (r : R) (x y : Fin n) : Formula R n
  | neg {n} : Formula R n → Formula R n
  | and {n} : Formula R n → Formula R n → Formula R n
  | ex {n} : Formula R (n+1) → Formula R n
  | hartig {n} : Formula R (n+1) → Formula R (n+1) → Formula R n

noncomputable def Formula.eval {R : Type} (A : Structure R) :
    {n : ℕ} → Formula R n → (Fin n → A.Carrier) → Prop
  | _, .falsum, _ => False
  | _, .eq x y, v => v x = v y
  | _, .rel r x y, v => A.rel r (v x) (v y) = true
  | _, .neg φ, v => ¬ φ.eval A v
  | _, .and φ ψ, v => φ.eval A v ∧ ψ.eval A v
  | _, .ex φ, v => ∃ a, φ.eval A (Fin.cons a v)
  | _, .hartig φ ψ, v =>
    Nat.card {a : A.Carrier // φ.eval A (Fin.cons a v)} =
    Nat.card {a : A.Carrier // ψ.eval A (Fin.cons a v)}

def Formula.holds {R : Type} (φ : Formula R 0) (A : Structure R) : Prop :=
  φ.eval A Fin.elim0

structure Interpretation (R T : Type) where
  domain : Formula R 2
  identify : Formula R 4
  relation : T → Formula R 4

namespace Interpretation

variable {R T : Type} (I : Interpretation R T) (A : Structure R)

abbrev Domain := {a : A.Carrier × A.Carrier // I.domain.eval A ![a.1,a.2]}

def link (a b : I.Domain A) : Prop :=
  I.identify.eval A ![a.val.1,a.val.2,b.val.1,b.val.2]

def classSetoid : Setoid (I.Domain A) :=
  Relation.EqvGen.setoid (I.link A)

abbrev Vertex := Quotient (I.classSetoid A)

noncomputable def apply : Structure T := by
  classical
  letI : Fintype (I.Domain A) := Fintype.ofFinite _
  letI : Fintype (I.Vertex A) := Fintype.ofFinite _
  exact {
    Carrier := I.Vertex A
    finite := inferInstance
    rel := fun r x y => decide (∃ a b : I.Domain A,
      Quotient.mk (I.classSetoid A) a = x ∧
      Quotient.mk (I.classSetoid A) b = y ∧
      (I.relation r).eval A ![a.val.1,a.val.2,b.val.1,b.val.2]) }

end Interpretation

structure Program (InputSymbols : Type) where
  StateSymbols : Type
  stateFinite : Fintype StateSymbols
  init : Interpretation InputSymbols StateSymbols
  step : Interpretation StateSymbols StateSymbols
  halt : Formula StateSymbols 0
  output : Formula StateSymbols 0

namespace Program

variable {R : Type} (P : Program R)

noncomputable def state (A : Structure R) : ℕ → Structure P.StateSymbols
  | 0 => P.init.apply A
  | j+1 => P.step.apply (state A j)

def haltsAt (A : Structure R) (j : ℕ) : Prop :=
  P.halt.holds (P.state A j) ∧ ∀ k < j, ¬ P.halt.holds (P.state A k)

noncomputable def cost (A : Structure R) (j : ℕ) : ℕ :=
  (j+1) + ∑ k ∈ Finset.range (j+1), Fintype.card (P.state A k).Carrier

def accepts (A : Structure R) : Prop :=
  ∃ j, P.haltsAt A j ∧ P.output.holds (P.state A j)

def polynomiallyBounded : Prop :=
  ∃ c d : ℕ, ∀ A : Structure R, ∃ j,
    P.haltsAt A j ∧ P.cost A j ≤ c * (Fintype.card A.Carrier + 1)^d

def decides (Q : Structure R → Prop) : Prop :=
  P.polynomiallyBounded ∧ ∀ A, P.accepts A ↔ Q A

end Program

def NondefinableByInterpretations {R : Type} (Q : Structure R → Prop) : Prop :=
  ¬ ∃ P : Program R, P.decides Q

end CPTSeparation.Interpretations

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

@[simp] theorem ofFinset_inj {s t : Finset (HF A)} : ofFinset s = ofFinset t ↔ s = t :=
  ⟨fun h => by simpa using congrArg elements h,fun h => congrArg ofFinset h⟩

def singleton (a : HF A) : HF A := ofFinset {a}

def pair (a b : HF A) : HF A := double (singleton a) (double a b)

@[simp] theorem mem_singleton (x a : HF A) : x ∈ singleton a ↔ x = a := by simp [singleton]

@[simp] theorem mem_double (x a b : HF A) : x ∈ double a b ↔ x = a ∨ x = b := by simp [double]

@[simp] theorem singleton_inj {a b : HF A} : singleton a = singleton b ↔ a = b := by simp [singleton]

@[simp] theorem map_singleton (f : A → B) (a : HF A) : map f (singleton a) = singleton (map f a) := by simp [singleton]

@[simp] theorem map_double (f : A → B) (a b : HF A) : map f (double a b) = double (map f a) (map f b) := by
  simp only [double,map_ofFinset,image_insert,image_singleton]
  apply ofFinset_inj.mpr
  ext x
  simp

@[simp] theorem map_pair (f : A → B) (a b : HF A) : map f (pair a b) = pair (map f a) (map f b) := by simp [pair]

theorem pair_injective {a b c d : HF A} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have first (a b : HF A) : ∀ u ∈ pair a b, a ∈ u := by
    intro u hu
    rcases (mem_double _ _ _).mp hu with rfl|rfl <;> simp
  have hac : a = c := by
    have hm : singleton c ∈ pair a b := by rw [h]; simp [pair]
    exact (mem_singleton _ _).mp (first a b _ hm)
  subst c
  have union (a b x : HF A) : (∃ u ∈ pair a b, x ∈ u) ↔ x = a ∨ x = b := by
    simp only [pair,mem_double]
    aesop
  have hb : b = a ∨ b = d := by
    apply (union a d b).mp
    rw [← h]
    exact (union a b b).mpr (Or.inr rfl)
  have hd : d = a ∨ d = b := by
    apply (union a b d).mp
    rw [h]
    exact (union a d d).mpr (Or.inr rfl)
  exact ⟨rfl,by rcases hb with hba|hbd; rcases hd with hda|hdb <;> simp_all; exact hbd⟩

@[simp] theorem pair_eq_pair {a b c d : HF A} : pair a b = pair c d ↔ a = c ∧ b = d :=
  ⟨pair_injective,fun ⟨h,h'⟩ => by rw [h,h']⟩

@[simp] theorem ordinal_isSet (i : ℕ) : isSet (ordinal (A := A) i) = true := by cases i <;> simp [ordinal]

theorem mem_ordinal (x : HF A) (i : ℕ) : x ∈ ordinal i ↔ ∃ k < i, x = ordinal k := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    change x ∈ ofFinset (insert (ordinal i) (elements (ordinal i))) ↔ _
    simp only [mem_ofFinset,mem_insert]
    change x = ordinal i ∨ x ∈ ordinal i ↔ _
    rw [ih]
    constructor
    · rintro (rfl|⟨k,hk,rfl⟩)
      · exact ⟨i,by omega,rfl⟩
      · exact ⟨k,by omega,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      by_cases hki : k = i
      · exact Or.inl (congrArg ordinal hki)
      · exact Or.inr ⟨k,by omega,rfl⟩

theorem ordinal_injective : Function.Injective (ordinal (A := A)) := by
  intro i j hij
  by_contra hn
  rcases lt_or_gt_of_ne hn with h|h
  · have hm := (mem_ordinal (ordinal (A := A) i) j).mpr ⟨i,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)
  · have hm := (mem_ordinal (ordinal (A := A) j) i).mpr ⟨j,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)

@[simp] theorem map_ordinal (f : A → B) (i : ℕ) : map f (ordinal i) = ordinal i := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    simp only [ordinal,map_ofFinset,image_insert,ih]
    rw [← elements_map,ih]
    apply ofFinset_inj.mpr
    ext x
    simp

def wrappers (a b : HF A) : Finset (HF A) := {pair a b,singleton a,double a b}

theorem wrappers_card_le (a b : HF A) : (wrappers a b).card ≤ 3 := by
  exact (card_insert_le _ _).trans (by have := card_insert_le (singleton a) {double a b}; simpa using Nat.add_le_add_right this 1)

theorem wrappers_trans {a b x y : HF A} (hx : x ∈ wrappers a b) (hy : y ∈ x) :
    y = a ∨ y = b ∨ y ∈ wrappers a b := by
  simp only [wrappers,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl
  · rcases (mem_double _ _ _).mp hy with rfl|rfl <;> simp [wrappers]
  · exact Or.inl ((mem_singleton _ _).mp hy)
  · rcases (mem_double _ _ _).mp hy with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CPTSeparation.Hereditary

namespace CPTSeparation.Interpretations

open Classical Finset Hereditary

variable {R T A : Type} (I : Interpretation R T) (S : Structure R)

def payload (e : S.Carrier → HF A) (C : I.Vertex S) : HF A :=
  ofFinset ((univ.filter (fun p : I.Domain S => Quotient.mk (I.classSetoid S) p = C)).image
    (fun p => pair (e p.val.1) (e p.val.2)))

theorem mem_payload (e : S.Carrier → HF A) (C : I.Vertex S) (x : HF A) :
    x ∈ payload I S e C ↔ ∃ p : I.Domain S,
      Quotient.mk (I.classSetoid S) p = C ∧ x = pair (e p.val.1) (e p.val.2) := by
  simp only [payload,mem_ofFinset,mem_image,mem_filter,mem_univ,true_and]
  exact exists_congr (fun p => and_congr_right (fun _ => eq_comm))

theorem payload_injective (e : S.Carrier → HF A) (he : Function.Injective e) :
    Function.Injective (payload I S e) := by
  intro C D h
  obtain ⟨p,rfl⟩ := Quotient.exists_rep C
  have hm : pair (e p.val.1) (e p.val.2) ∈ payload I S e (Quotient.mk _ p) :=
    (mem_payload I S e _ _).mpr ⟨p,rfl,rfl⟩
  rw [h] at hm
  obtain ⟨q,hq,hpq⟩ := (mem_payload I S e D _).mp hm
  have hh := pair_injective hpq
  have heq : p = q := Subtype.ext (Prod.ext (he hh.1) (he hh.2))
  rw [heq]
  exact hq

def vertexCode (e : S.Carrier → HF A) (j : ℕ) (C : I.Vertex S) : HF A :=
  pair (ordinal j) (payload I S e C)

theorem vertexCode_injective (e : S.Carrier → HF A) (he : Function.Injective e) (j : ℕ) :
    Function.Injective (vertexCode I S e j) := by
  intro C D h
  exact payload_injective I S e he (pair_injective h).2

def pairFamily (e : S.Carrier → HF A) : Finset (HF A) :=
  univ.biUnion (fun p : I.Domain S => wrappers (e p.val.1) (e p.val.2))

def classFamily (e : S.Carrier → HF A) (j : ℕ) : Finset (HF A) :=
  univ.biUnion (fun C : I.Vertex S => insert (payload I S e C)
    (wrappers (ordinal j) (payload I S e C)))

theorem pairFamily_card_le (e : S.Carrier → HF A) :
    (pairFamily I S e).card ≤ 3*Fintype.card S.Carrier^2 := by
  calc
    (pairFamily I S e).card ≤ ∑ p : I.Domain S, (wrappers (e p.val.1) (e p.val.2)).card :=
      card_biUnion_le
    _ ≤ ∑ _p : I.Domain S, 3 := sum_le_sum (fun p _ => wrappers_card_le _ _)
    _ = 3*Fintype.card (I.Domain S) := by simp [mul_comm]
    _ ≤ 3*Fintype.card S.Carrier^2 := by
      apply Nat.mul_le_mul_left
      have h := Fintype.card_subtype_le (fun p : S.Carrier × S.Carrier => I.domain.eval S ![p.1,p.2])
      simpa only [Fintype.card_prod,pow_two] using h

theorem classFamily_card_le (e : S.Carrier → HF A) (j : ℕ) :
    (classFamily I S e j).card ≤ 4*Fintype.card (I.Vertex S) := by
  calc
    (classFamily I S e j).card ≤ ∑ C : I.Vertex S,
        (insert (payload I S e C) (wrappers (ordinal j) (payload I S e C))).card := card_biUnion_le
    _ ≤ ∑ _C : I.Vertex S, 4 := by
      apply sum_le_sum
      intro C _
      exact (card_insert_le _ _).trans (by have := wrappers_card_le (ordinal (A := A) j) (payload I S e C); omega)
    _ = 4*Fintype.card (I.Vertex S) := by simp [mul_comm]

theorem stage_family_transitive (e : S.Carrier → HF A) (j : ℕ) (F : Finset (HF A))
    (hF : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (he : ∀ a, e a ∈ F) (hj : ordinal j ∈ F) :
    ∀ x ∈ F ∪ pairFamily I S e ∪ classFamily I S e j,
    ∀ y, y ∈ x → y ∈ F ∪ pairFamily I S e ∪ classFamily I S e j := by
  intro x hx y hy
  have incF : F ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_left _ (mem_union_left _ hz)
  have incP : pairFamily I S e ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_left _ (mem_union_right _ hz)
  have incC : classFamily I S e j ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_right _ hz
  rcases mem_union.mp hx with hx|hx
  · rcases mem_union.mp hx with hx|hx
    · exact incF (hF x hx y hy)
    · obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx
      rcases wrappers_trans hp hy with h|h|h
      · rw [h]; exact incF (he _)
      · rw [h]; exact incF (he _)
      · exact incP (mem_biUnion.mpr ⟨p,mem_univ _,h⟩)
  · obtain ⟨C,_,hC⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hC with rfl|hC
    · obtain ⟨p,hp,hyp⟩ := (mem_payload I S e C y).mp hy
      apply incP
      apply mem_biUnion.mpr
      exact ⟨p,mem_univ _,by simp [hyp,wrappers]⟩
    · rcases wrappers_trans hC hy with h|h|h
      · rw [h]; exact incF hj
      · rw [h]; exact incC (mem_biUnion.mpr ⟨C,mem_univ _,mem_insert_self _ _⟩)
      · exact incC (mem_biUnion.mpr ⟨C,mem_univ _,mem_insert_of_mem h⟩)

end CPTSeparation.Interpretations

namespace CPTSeparation.Counting

open Classical Finset

variable {R D : Type*} (S : Structure R D) {m n k : ℕ}

def Definable (m n : ℕ) (P : (Fin n → D) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ v, φ.eval S v ↔ P (v ∘ args)

namespace Definable

variable {S} {P Q : (Fin n → D) → Prop}

theorem congr (h : Definable S m n P) (heq : ∀ v, P v ↔ Q v) : Definable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun v => (he v).trans (heq _)⟩

theorem reindex (h : Definable S m n P) (f : Fin n → Fin k) :
    Definable S m k (fun v => P (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun v => he v⟩
  intro i hi
  obtain ⟨j,_,rfl⟩ := mem_image.mp (hφ hi)
  exact mem_image.mpr ⟨f j,mem_univ _,rfl⟩

theorem falsum : Definable S m n (fun _ => False) := by
  intro args
  exact ⟨.falsum,by simp [Formula.free],fun _ => Iff.rfl⟩

theorem neg (h : Definable S m n P) : Definable S m n (fun v => ¬ P v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun v => not_congr (he v)⟩

theorem and (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∧ Q v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun v => and_congr (he v) (he' v)⟩

theorem or (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∨ Q v) :=
  (h.neg.and h'.neg).neg.congr (fun _ => by tauto)

theorem imp (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v → Q v) :=
  (h.neg.or h').congr (fun _ => by tauto)

theorem iff (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ↔ Q v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ => by tauto)

theorem equal (i j : Fin n) : Definable S m n (fun v => v i = v j) := by
  intro args
  refine ⟨.equal (args i) (args j),?_,fun _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩

theorem relation (r : R) (i j : Fin n) : Definable S m n (fun v => S.rel r (v i) (v j)) := by
  intro args
  refine ⟨.relation r (args i) (args j),?_,fun _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩

private theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

private theorem updated_args (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → D) (x : D) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

private theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∃ x, P (Fin.cons x v)) := by
  intro args
  obtain ⟨i,hi⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons i args)
  refine ⟨.ex i φ,free_binder hφ,?_⟩
  intro v
  apply exists_congr
  intro x
  simpa only [updated_args args i hi] using he (Function.update v i x)

theorem all {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∀ x, P (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ => by simp)

theorem exact {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) (k : ℕ) :
    Definable S m n (fun v => Nonempty ({x : D // P (Fin.cons x v)} ≃ Fin k)) := by
  intro args
  obtain ⟨i,hi⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons i args)
  refine ⟨.exact i k φ,free_binder hφ,?_⟩
  intro v
  let e : {x : D // φ.eval S (Function.update v i x)} ≃ {x : D // P (Fin.cons x (v ∘ args))} :=
    Equiv.subtypeEquivRight (fun x => by simpa only [updated_args args i hi] using he (Function.update v i x))
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem exists_finset {ι : Type*} {P : ι → (Fin n → D) → Prop} (t : Finset ι)
    (h : ∀ i ∈ t, Definable S m n (P i)) : Definable S m n (fun v => ∃ i ∈ t, P i v) := by
  induction t using Finset.induction_on with
  | empty => exact (falsum (S := S)).congr (fun _ => by simp)
  | @insert i t hi ih =>
    exact ((h i (mem_insert_self _ _)).or (ih (fun j hj => h j (mem_insert_of_mem hj)))).congr
      (fun v => by simp only [mem_insert,exists_eq_or_imp])

theorem bounded_hartig {P Q : (Fin (n+1) → D) → Prop}
    (hP : Definable S m (n+1) P) (hQ : Definable S m (n+1) Q) (hn : n < m) (B : ℕ) :
    Definable S m n (fun v => ∃ k ≤ B,
      Nonempty ({x : D // P (Fin.cons x v)} ≃ Fin k) ∧
      Nonempty ({x : D // Q (Fin.cons x v)} ≃ Fin k)) := by
  apply (exists_finset (range (B+1)) (fun k _ => (hP.exact hn k).and (hQ.exact hn k))).congr
  intro v
  simp only [mem_range,Nat.lt_succ_iff]

end Definable

end CPTSeparation.Counting

namespace CPTSeparation.HFCoding

open Classical Finset Hereditary Counting

variable {A R : Type} {d : Set (HF A)}

abbrev Domain (d : Set (HF A)) := {x : HF A // x ∈ d}

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

variable (S : Counting.Structure R (Domain d)) {m : ℕ}

def SingletonTest (u a : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a

def DoubleTest (u a b : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a ∨ w = b

include hd

theorem singletonTest_iff (u a : Domain d) : SingletonTest u a ↔ u.val = Hereditary.singleton a.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ Hereditary.singleton a.val
    rw [Hereditary.mem_singleton]
    constructor
    · intro hw
      exact congrArg Subtype.val ((h ⟨w,hd _ u.property _ hw⟩).mp hw)
    · rintro rfl
      exact (h a).mpr rfl
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,Hereditary.mem_singleton]
      exact Subtype.val_injective.eq_iff

theorem doubleTest_iff (u a b : Domain d) : DoubleTest u a b ↔ u.val = double a.val b.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ double a.val b.val
    rw [mem_double]
    constructor
    · intro hw
      rcases (h ⟨w,hd _ u.property _ hw⟩).mp hw with h|h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl|rfl)
      · exact (h a).mpr (Or.inl rfl)
      · exact (h b).mpr (Or.inr rfl)
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,mem_double]
      exact or_congr Subtype.val_injective.eq_iff Subtype.val_injective.eq_iff

def PairTest (z a b : Domain d) : Prop :=
  ∃ u v : Domain d, SingletonTest u a ∧ DoubleTest v a b ∧ DoubleTest z u v

theorem pairTest_iff (z a b : Domain d) : PairTest z a b ↔ z.val = pair a.val b.val := by
  constructor
  · rintro ⟨u,v,hu,hv,hz⟩
    rw [singletonTest_iff hd] at hu
    rw [doubleTest_iff hd] at hv hz
    simpa only [hu,hv,pair] using hz
  · intro hz
    have hu : Hereditary.singleton a.val ∈ d := hd _ z.property _ (by rw [hz]; simp [pair])
    have hv : double a.val b.val ∈ d := hd _ z.property _ (by rw [hz]; simp [pair])
    refine ⟨⟨Hereditary.singleton a.val,hu⟩,⟨double a.val b.val,hv⟩,?_,?_,?_⟩
    · exact (singletonTest_iff hd _ _).mpr rfl
    · exact (doubleTest_iff hd _ _ _).mpr rfl
    · exact (doubleTest_iff hd _ _ _).mpr hz

variable (hmem : Definable S m 2 (fun v => (v 0).val ∈ (v 1).val))

variable (hset : Definable S m 1 (fun v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hmem hset hm

private theorem singleton_value_definable :
    Definable S m 2 (fun v => (v 0).val = Hereditary.singleton (v 1).val) := by
  have hs : Definable S m 2 (fun v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 2)
  have hbody : Definable S m 3 (fun v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2) := by
    have hmem' : Definable S m 3 (fun v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 3)
    exact hmem'.iff (Definable.equal 0 2)
  apply (hs.and (hbody.all (by omega))).congr
  intro v
  exact singletonTest_iff hd (v 0) (v 1)

theorem singleton_definable : Definable S m 2 (fun v => SingletonTest (v 0) (v 1)) := by
  apply (singleton_value_definable hd S hmem hset hm).congr
  intro v
  exact (singletonTest_iff hd (v 0) (v 1)).symm

private theorem double_value_definable :
    Definable S m 3 (fun v => (v 0).val = double (v 1).val (v 2).val) := by
  have hs : Definable S m 3 (fun v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 3)
  have hbody : Definable S m 4 (fun v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2 ∨ v 0 = v 3) := by
    have hmem' : Definable S m 4 (fun v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 4)
    exact hmem'.iff ((Definable.equal 0 2).or (Definable.equal 0 3))
  apply (hs.and (hbody.all (by omega))).congr
  intro v
  exact doubleTest_iff hd (v 0) (v 1) (v 2)

theorem double_definable : Definable S m 3 (fun v => DoubleTest (v 0) (v 1) (v 2)) := by
  apply (double_value_definable hd S hmem hset hm).congr
  intro v
  exact (doubleTest_iff hd (v 0) (v 1) (v 2)).symm

theorem pair_definable : Definable S m 3 (fun v => (v 0).val = pair (v 1).val (v 2).val) := by
  have h1 : Definable S m 5 (fun v => SingletonTest (v 1) (v 3)) := by
    simpa using (singleton_definable hd S hmem hset hm).reindex (![1,3] : Fin 2 → Fin 5)
  have h2 : Definable S m 5 (fun v => DoubleTest (v 0) (v 3) (v 4)) := by
    simpa using (double_definable hd S hmem hset hm).reindex (![0,3,4] : Fin 3 → Fin 5)
  have h3 : Definable S m 5 (fun v => DoubleTest (v 2) (v 1) (v 0)) := by
    simpa using (double_definable hd S hmem hset hm).reindex (![2,1,0] : Fin 3 → Fin 5)
  have hp := ((h1.and (h2.and h3)).ex (by omega)).ex (by omega)
  apply hp.congr
  intro v
  exact pairTest_iff hd (v 0) (v 1) (v 2)

theorem ordinal_definable (hpure : ∀ i, ordinal (A := A) i ∈ d) (i : ℕ) :
    Definable S m 1 (fun v => (v 0).val = ordinal i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hor : Definable S m 2 (fun v => ∃ k ∈ range i, (v 0).val = ordinal k) := by
      apply Definable.exists_finset
      intro k hk
      simpa using (ih k (mem_range.mp hk)).reindex (![0] : Fin 1 → Fin 2)
    have hbody := (hmem.iff hor).all (by omega : 1 < m)
    apply (hset.and hbody).congr
    intro v
    change (isSet (v 0).val = true ∧ ∀ w : Domain d,
      w.val ∈ (v 0).val ↔ ∃ k ∈ range i, w.val = ordinal k) ↔ _
    constructor
    · rintro ⟨hv,h⟩
      apply ext_sets hv (ordinal_isSet i)
      intro w
      rw [mem_ordinal]
      constructor
      · intro hw
        obtain ⟨k,hk,hkw⟩ := (h ⟨w,hd _ (v 0).property _ hw⟩).mp hw
        exact ⟨k,mem_range.mp hk,hkw⟩
      · rintro ⟨k,hk,rfl⟩
        exact (h ⟨ordinal k,hpure k⟩).mpr ⟨k,mem_range.mpr hk,rfl⟩
    · intro hv
      refine ⟨by rw [hv]; exact ordinal_isSet i,?_⟩
      intro w
      rw [hv,mem_ordinal]
      simp only [mem_range]

end CPTSeparation.HFCoding

namespace CPTSeparation.Counting

open Classical Finset

variable {R ι : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m n k : ℕ}

def UniformDefinable (m n : ℕ) (P : ∀ i, (Fin n → D i) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ i v, φ.eval (S i) v ↔ P i (v ∘ args)

namespace UniformDefinable

variable {S} {P Q : ∀ i, (Fin n → D i) → Prop}

theorem congr (h : UniformDefinable S m n P) (heq : ∀ i v, P i v ↔ Q i v) :
    UniformDefinable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun i v => (he i v).trans (heq _ _)⟩

theorem reindex (h : UniformDefinable S m n P) (f : Fin n → Fin k) :
    UniformDefinable S m k (fun i v => P i (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun i v => he i v⟩
  intro j hj
  obtain ⟨l,_,rfl⟩ := mem_image.mp (hφ hj)
  exact mem_image.mpr ⟨f l,mem_univ _,rfl⟩

theorem falsum : UniformDefinable S m n (fun _ _ => False) :=
  fun _ => ⟨.falsum,by simp [Formula.free],fun _ _ => Iff.rfl⟩

theorem neg (h : UniformDefinable S m n P) : UniformDefinable S m n (fun i v => ¬ P i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun i v => not_congr (he i v)⟩

theorem and (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∧ Q i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun i v => and_congr (he i v) (he' i v)⟩

theorem or (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∨ Q i v) :=
  (h.neg.and h'.neg).neg.congr (fun _ _ => by tauto)

theorem imp (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v → Q i v) :=
  (h.neg.or h').congr (fun _ _ => by tauto)

theorem iff (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ↔ Q i v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ _ => by tauto)

theorem equal (a b : Fin n) : UniformDefinable S m n (fun _ v => v a = v b) := by
  intro args
  refine ⟨.equal (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

theorem relation (r : R) (a b : Fin n) :
    UniformDefinable S m n (fun i v => (S i).rel r (v a) (v b)) := by
  intro args
  refine ⟨.relation r (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

private theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

private theorem updated_args {X : Type*} (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → X) (x : X) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

private theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∃ x, P i (Fin.cons x v)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.ex a φ,free_binder hφ,?_⟩
  intro i v
  apply exists_congr
  intro x
  simpa only [updated_args args a ha] using he i (Function.update v a x)

theorem all {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∀ x, P i (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ _ => by simp)

theorem exact {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) (k : ℕ) :
    UniformDefinable S m n (fun i v => Nonempty ({x : D i // P i (Fin.cons x v)} ≃ Fin k)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.exact a k φ,free_binder hφ,?_⟩
  intro i v
  let e : {x : D i // φ.eval (S i) (Function.update v a x)} ≃ {x : D i // P i (Fin.cons x (v ∘ args))} :=
    Equiv.subtypeEquivRight (fun x => by simpa only [updated_args args a ha] using he i (Function.update v a x))
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem exists_finset {κ : Type*} {P : κ → ∀ i, (Fin n → D i) → Prop} (t : Finset κ)
    (h : ∀ a ∈ t, UniformDefinable S m n (P a)) : UniformDefinable S m n (fun i v => ∃ a ∈ t, P a i v) := by
  induction t using Finset.induction_on with
  | empty => exact (falsum (S := S)).congr (fun _ _ => by simp)
  | @insert a t ha ih =>
    exact ((h a (mem_insert_self _ _)).or (ih (fun b hb => h b (mem_insert_of_mem hb)))).congr
      (fun _ _ => by simp only [mem_insert,exists_eq_or_imp])

theorem bounded_hartig {P Q : ∀ i, (Fin (n+1) → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q) (hn : n < m) (B : ℕ) :
    UniformDefinable S m n (fun i v => ∃ k ≤ B,
      Nonempty ({x : D i // P i (Fin.cons x v)} ≃ Fin k) ∧
      Nonempty ({x : D i // Q i (Fin.cons x v)} ≃ Fin k)) := by
  apply (exists_finset (range (B+1)) (fun k _ => (hP.exact hn k).and (hQ.exact hn k))).congr
  intro i v
  simp only [mem_range,Nat.lt_succ_iff]

end UniformDefinable

end CPTSeparation.Counting

namespace CPTSeparation.HFCoding

open Classical Finset Hereditary Counting

variable {ι R : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hmem hset hm

theorem uniform_singleton : UniformDefinable S m 2 (fun _ v => SingletonTest (v 0) (v 1)) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 2)
  have hbody : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2) := by
    have hmem' : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 3)
    exact hmem'.iff (UniformDefinable.equal 0 2)
  exact hs.and (hbody.all (by omega))

theorem uniform_double : UniformDefinable S m 3 (fun _ v => DoubleTest (v 0) (v 1) (v 2)) := by
  have hs : UniformDefinable S m 3 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 3)
  have hbody : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2 ∨ v 0 = v 3) := by
    have hmem' : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 4)
    exact hmem'.iff ((UniformDefinable.equal 0 2).or (UniformDefinable.equal 0 3))
  exact hs.and (hbody.all (by omega))

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

include hd

theorem uniform_pair : UniformDefinable S m 3 (fun _ v => (v 0).val = pair (v 1).val (v 2).val) := by
  have h1 : UniformDefinable S m 5 (fun _ v => SingletonTest (v 1) (v 3)) := by
    simpa using (uniform_singleton S hmem hset hm).reindex (![1,3] : Fin 2 → Fin 5)
  have h2 : UniformDefinable S m 5 (fun _ v => DoubleTest (v 0) (v 3) (v 4)) := by
    simpa using (uniform_double S hmem hset hm).reindex (![0,3,4] : Fin 3 → Fin 5)
  have h3 : UniformDefinable S m 5 (fun _ v => DoubleTest (v 2) (v 1) (v 0)) := by
    simpa using (uniform_double S hmem hset hm).reindex (![2,1,0] : Fin 3 → Fin 5)
  have hp := ((h1.and (h2.and h3)).ex (by omega)).ex (by omega)
  apply hp.congr
  intro i v
  exact pairTest_iff (hd i) (v 0) (v 1) (v 2)

theorem uniform_ordinal (hpure : ∀ i k, ordinal (A := A i) k ∈ d i) (k : ℕ) :
    UniformDefinable S m 1 (fun _ v => (v 0).val = ordinal k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hor : UniformDefinable S m 2 (fun _ v => ∃ j ∈ range k, (v 0).val = ordinal j) := by
      apply UniformDefinable.exists_finset
      intro j hj
      simpa using (ih j (mem_range.mp hj)).reindex (![0] : Fin 1 → Fin 2)
    have hbody := (hmem.iff hor).all (by omega : 1 < m)
    apply (hset.and hbody).congr
    intro i v
    change (isSet (v 0).val = true ∧ ∀ w : Domain (d i),
      w.val ∈ (v 0).val ↔ ∃ j ∈ range k, w.val = ordinal j) ↔ _
    constructor
    · rintro ⟨hv,h⟩
      apply ext_sets hv (ordinal_isSet k)
      intro w
      rw [mem_ordinal]
      constructor
      · intro hw
        obtain ⟨j,hj,hjw⟩ := (h ⟨w,hd i _ (v 0).property _ hw⟩).mp hw
        exact ⟨j,mem_range.mp hj,hjw⟩
      · rintro ⟨j,hj,rfl⟩
        exact (h ⟨ordinal j,hpure i j⟩).mpr ⟨j,mem_range.mpr hj,rfl⟩
    · intro hv
      refine ⟨by rw [hv]; exact ordinal_isSet k,?_⟩
      intro w
      rw [hv,mem_ordinal]
      simp only [mem_range]

end CPTSeparation.HFCoding

namespace CPTSeparation.Interpretations

open Classical Finset Hereditary

variable {R T : Type} {S S' : Structure R}

structure Structure.Iso (S S' : Structure R) where
  equiv : S.Carrier ≃ S'.Carrier
  rel : ∀ r x y, S.rel r x y = S'.rel r (equiv x) (equiv y)

namespace Structure.Iso

variable (e : S.Iso S')

def symm : S'.Iso S where
  equiv := e.equiv.symm
  rel r x y := by simpa using (e.rel r (e.equiv.symm x) (e.equiv.symm y)).symm

theorem eval {n : ℕ} (φ : Formula R n) (v : Fin n → S.Carrier) :
    φ.eval S v ↔ φ.eval S' (e.equiv ∘ v) := by
  induction φ with
  | falsum => rfl
  | eq x y => simp only [Formula.eval,Function.comp_apply,Equiv.apply_eq_iff_eq]
  | rel r x y => simp only [Formula.eval,Function.comp_apply,e.rel]
  | neg φ ih => exact not_congr (ih v)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | ex φ ih =>
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨e.equiv a,?_⟩
      simpa only [Fin.comp_cons] using (ih (Fin.cons a v)).mp ha
    · rintro ⟨b,hb⟩
      obtain ⟨a,rfl⟩ := e.equiv.surjective b
      exact ⟨a,(ih (Fin.cons a v)).mpr (by simpa only [Fin.comp_cons] using hb)⟩
  | hartig φ ψ ihφ ihψ =>
    have hφ : ∀ a, φ.eval S (Fin.cons a v) ↔ φ.eval S' (Fin.cons (e.equiv a) (e.equiv ∘ v)) :=
      fun a => by simpa only [Fin.comp_cons] using ihφ (Fin.cons a v)
    have hψ : ∀ a, ψ.eval S (Fin.cons a v) ↔ ψ.eval S' (Fin.cons (e.equiv a) (e.equiv ∘ v)) :=
      fun a => by simpa only [Fin.comp_cons] using ihψ (Fin.cons a v)
    change Nat.card _ = Nat.card _ ↔ Nat.card _ = Nat.card _
    rw [Nat.card_congr (e.equiv.subtypeEquiv (q := fun a : S'.Carrier => φ.eval S' (Fin.cons a (e.equiv ∘ v))) hφ),Nat.card_congr (e.equiv.subtypeEquiv (q := fun a : S'.Carrier => ψ.eval S' (Fin.cons a (e.equiv ∘ v))) hψ)]

end Structure.Iso

namespace Interpretation

variable (I : Interpretation R T) (e : S.Iso S')

def domainEquiv : I.Domain S ≃ I.Domain S' :=
  (Equiv.prodCongr e.equiv e.equiv).subtypeEquiv (fun a => by
    have h := e.eval I.domain ![a.1,a.2]
    have hh : e.equiv ∘ ![a.1,a.2] = ![e.equiv a.1,e.equiv a.2] := by
      ext i; fin_cases i <;> rfl
    simpa only [hh,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd] using h)

@[simp] theorem domainEquiv_val (a : I.Domain S) :
    (I.domainEquiv e a).val = (e.equiv a.val.1,e.equiv a.val.2) := rfl

theorem link_equiv (a b : I.Domain S) : I.link S a b ↔ I.link S' (I.domainEquiv e a) (I.domainEquiv e b) := by
  have h := e.eval I.identify ![a.val.1,a.val.2,b.val.1,b.val.2]
  have hh : e.equiv ∘ ![a.val.1,a.val.2,b.val.1,b.val.2] =
      ![e.equiv a.val.1,e.equiv a.val.2,e.equiv b.val.1,e.equiv b.val.2] := by
    ext i; fin_cases i <;> rfl
  simpa only [link,domainEquiv_val,hh] using h

private theorem eqvGen_map {α β : Type} (r : α → α → Prop) (s : β → β → Prop)
    (f : α → β) (hf : ∀ a b, r a b → s (f a) (f b)) {a b : α} :
    Relation.EqvGen r a b → Relation.EqvGen s (f a) (f b) := by
  intro h
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y h ih => exact .symm _ _ ih
  | trans x y z h h' ih ih' => exact .trans _ _ _ ih ih'

theorem class_equiv (a b : I.Domain S) :
    I.classSetoid S a b ↔ I.classSetoid S' (I.domainEquiv e a) (I.domainEquiv e b) := by
  change Relation.EqvGen (I.link S) a b ↔ Relation.EqvGen (I.link S') _ _
  constructor
  · exact eqvGen_map _ _ (I.domainEquiv e) (fun a b => (I.link_equiv e a b).mp)
  · intro h
    have hm := eqvGen_map (I.link S') (I.link S) (I.domainEquiv e).symm
      (fun a b hab => (I.link_equiv e ((I.domainEquiv e).symm a) ((I.domainEquiv e).symm b)).mpr
        (by simpa using hab)) h
    simpa using hm

def vertexEquiv : I.Vertex S ≃ I.Vertex S' := Quotient.congr (I.domainEquiv e) (I.class_equiv e)

@[simp] theorem vertexEquiv_mk (a : I.Domain S) :
    I.vertexEquiv e (Quotient.mk _ a) = Quotient.mk _ (I.domainEquiv e a) := rfl

def applyIso : (I.apply S).Iso (I.apply S') where
  equiv := I.vertexEquiv e
  rel r C D := by
    simp only [Interpretation.apply,decide_eq_decide]
    constructor
    · rintro ⟨a,b,ha,hb,hr⟩
      refine ⟨I.domainEquiv e a,I.domainEquiv e b,?_,?_,?_⟩
      · exact congrArg (I.vertexEquiv e) ha
      · exact congrArg (I.vertexEquiv e) hb
      · have hh := (e.eval (I.relation r) ![a.val.1,a.val.2,b.val.1,b.val.2]).mp hr
        have hv : (fun x => e.equiv (![a.val.1,a.val.2,b.val.1,b.val.2] x)) =
            ![(I.domainEquiv e a).val.1,(I.domainEquiv e a).val.2,(I.domainEquiv e b).val.1,(I.domainEquiv e b).val.2] := by
          ext i; fin_cases i <;> rfl
        exact hv ▸ hh
    · rintro ⟨a,b,ha,hb,hr⟩
      obtain ⟨a,rfl⟩ := (I.domainEquiv e).surjective a
      obtain ⟨b,rfl⟩ := (I.domainEquiv e).surjective b
      refine ⟨a,b,?_,?_,?_⟩
      · apply (I.vertexEquiv e).injective
        exact ha
      · apply (I.vertexEquiv e).injective
        exact hb
      · apply (e.eval (I.relation r) ![a.val.1,a.val.2,b.val.1,b.val.2]).mpr
        have hv : (fun x => e.equiv (![a.val.1,a.val.2,b.val.1,b.val.2] x)) =
            ![(I.domainEquiv e a).val.1,(I.domainEquiv e a).val.2,(I.domainEquiv e b).val.1,(I.domainEquiv e b).val.2] := by
          ext i; fin_cases i <;> rfl
        change Formula.eval S' (I.relation r) (fun x => e.equiv (![a.val.1,a.val.2,b.val.1,b.val.2] x))
        rw [hv]
        exact hr

end Interpretation

end CPTSeparation.Interpretations

end

end OAI
