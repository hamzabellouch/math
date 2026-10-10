import OAI.Computability.WitnessedChoice.Model

namespace OAI

universe u v w

namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A : Type u} {B : Type v}

attribute [local instance] instDecidableEqHF

@[simp] theorem mk_out (x : HF A) : mk (Quotient.out x) = x := Quotient.out_eq x

@[simp] theorem isSet_mk (l : Lists A) : isSet (mk l) = l.1 := rfl

@[simp] theorem isSet_atom (a : A) : isSet (atom a) = false := rfl

@[simp] theorem elements_mk (l : Lists A) : elements (mk l) = rawElements l := rfl

@[simp] theorem elements_atom (a : A) : elements (atom a) = ∅ := by
  classical
  change rawElements (Lists.atom a) = ∅
  simp [rawElements, Lists.toList]

@[simp] theorem not_mem_atom (x : HF A) (a : A) : ¬ x ∈ atom a := by
  change ¬ x ∈ elements (atom a)
  simp

theorem atom_injective : Function.Injective (atom : A → HF A) := by
  intro a b h
  have h' := Lists.equiv_atom.mp (mk_eq_mk.mp h)
  cases h'
  rfl

@[simp] theorem isSet_ofFinset (s : Finset (HF A)) : isSet (ofFinset s) = true := rfl

@[simp] theorem elements_ofFinset (s : Finset (HF A)) : elements (ofFinset s) = s := by
  classical
  ext x
  simp only [ofFinset, elements_mk, rawElements, Lists.to_ofList, Finset.mem_image,
    List.mem_toFinset]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨l, ⟨y,hy,rfl⟩,h⟩
    rw [mk_out] at h
    exact h ▸ hy
  · intro hx
    exact ⟨Quotient.out x, ⟨x,hx,rfl⟩, mk_out x⟩

@[simp] theorem mem_ofFinset (x : HF A) (s : Finset (HF A)) : x ∈ ofFinset s ↔ x ∈ s := by
  change x ∈ elements (ofFinset s) ↔ x ∈ s
  rw [elements_ofFinset]

theorem ext_sets {x y : HF A} (hx : isSet x = true) (hy : isSet y = true)
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ l =>
    induction y using Quotient.inductionOn with
    | _ r =>
      rcases l with ⟨(_ | _), l⟩ <;> (try cases hx)
      rcases r with ⟨(_ | _), r⟩ <;> (try cases hy)
      apply mk_eq_mk.mpr
      apply Lists.Equiv.antisymm
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' r)).mp
        apply (h (mk a)).mp
        exact (mem_mk a (Lists.of' l)).mpr ⟨a,ha,Lists.Equiv.refl a⟩
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' l)).mp
        apply (h (mk a)).mpr
        exact (mem_mk a (Lists.of' r)).mpr ⟨a,ha,Lists.Equiv.refl a⟩

theorem ofFinset_elements {x : HF A} (hx : isSet x = true) : ofFinset (elements x) = x := by
  apply ext_sets (isSet_ofFinset _) hx
  intro z
  rw [mem_ofFinset]
  rfl

theorem atom_or_set (x : HF A) : (∃ a, x = atom a) ∨ x = ofFinset (elements x) := by
  induction x using Quotient.inductionOn with
  | _ l =>
    rcases l with ⟨(_ | _), l⟩
    · cases l with
      | atom a => exact Or.inl ⟨a,rfl⟩
    · exact Or.inr (ofFinset_elements rfl).symm

@[simp] theorem rank_mk (l : Lists A) : rank (mk l) = rawRank l := rfl

@[simp] theorem rank_atom (a : A) : rank (atom a) = 0 := rfl

theorem mem_wellFounded : WellFounded (fun x y : HF A => x ∈ y) :=
  (measure rank).wf.mono (fun _ _ h => rank_lt_of_mem h)

@[simp] theorem map_atom (f : A → B) (a : A) : map f (atom a) = atom (f a) := rfl

@[simp] theorem isSet_map (f : A → B) (x : HF A) : isSet (map f x) = isSet x := by
  induction x using Quotient.inductionOn with
  | _ l => rfl

theorem elements_map (f : A → B) (x : HF A) :
    elements (map f x) = (elements x).image (map f) := by
  classical
  induction x using Quotient.inductionOn with
  | _ l =>
    change (rawMap f l).toList.toFinset.image mk =
      (l.toList.toFinset.image mk).image (map f)
    rw [Finset.image_image]
    have ht : (rawMap f l).toList = l.toList.map (rawMap f) := toList_rawMap' f l.2
    rw [ht]
    ext z
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩
      exact ⟨a,ha,h⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨rawMap f a,⟨a,ha,rfl⟩,h⟩

@[simp] theorem map_ofFinset (f : A → B) (s : Finset (HF A)) :
    map f (ofFinset s) = ofFinset (s.image (map f)) := by
  classical
  apply ext_sets (by simp) (by simp)
  intro z
  change z ∈ elements (map f (ofFinset s)) ↔ z ∈ elements (ofFinset (s.image (map f)))
  rw [elements_map, elements_ofFinset, elements_ofFinset]

def mapEquiv (e : A ≃ B) : HF A ≃ HF B where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    rw [map_comp]
    have h : (e.symm : B → A) ∘ (e : A → B) = id := by funext a; simp
    rw [h,map_id]
  right_inv x := by
    rw [map_comp]
    have h : (e : A → B) ∘ (e.symm : B → A) = id := by funext a; simp
    rw [h,map_id]

@[simp] theorem smul_atom {G : Type w} [Group G] [MulAction G A] (g : G) (a : A) :
    g • atom a = atom (g • a) := rfl

@[simp] theorem smul_ofFinset {G : Type w} [Group G] [MulAction G A] (g : G) (s : Finset (HF A)) :
    g • ofFinset s = ofFinset (s.image (fun x => g • x)) := map_ofFinset _ _

def Supports {G : Type w} [Group G] [MulAction G A] {k : ℕ}
    (alpha : Fin k → A) (x : HF A) : Prop :=
  ∀ g : G, (∀ i, g • alpha i = alpha i) → g • x = x

def Supported {G : Type w} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∃ alpha : Fin s → A, Supports (G := G) alpha x

def HereditarilySupported {G : Type w} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∀ y, Relation.ReflTransGen (fun a b : HF A => a ∈ b) y x → Supported (G := G) s y

end



noncomputable section

open Classical Finset

variable {A : Type u} {B : Type v}

@[simp] theorem ofFinset_inj {s t : Finset (HF A)} : ofFinset s = ofFinset t ↔ s = t :=
  ⟨fun h => by simpa using congrArg elements h,fun h => congrArg ofFinset h⟩

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

end

end WitnessedSeparation.Hereditary

namespace WitnessedSeparation

example : Fintype.card Symbol = 8 := by decide

end WitnessedSeparation

namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A : Type u} {B : Type v}

attribute [local instance] instDecidableEqHF_1

@[simp] lemma mem_closure_self (x : HF A) : x ∈ closure x := by rw [closure]; simp

lemma closure_member_subset {x y : HF A} (h : y ∈ x) : closure y ⊆ closure x := by
  nth_rw 2 [closure]
  intro z hz
  simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  exact Or.inr ⟨y,h,hz⟩

lemma mem_closure_iff (x y : HF A) : x ∈ closure y ↔
    Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y := by
  constructor
  · intro h
    induction y using (measure rank).wf.induction with
    | h y ih =>
      rw [closure] at h
      rcases mem_insert.mp h with rfl | hm
      · exact .refl
      · obtain ⟨z,hz,hxz⟩ := mem_biUnion.mp hm
        exact (ih z.val (rank_lt_of_mem z.property) hxz).tail z.property
  · intro h
    induction h with
    | refl => exact mem_closure_self _
    | tail hab hbc ih => exact closure_member_subset hbc ih

lemma closure_transitive {x y z : HF A} (hxy : y ∈ closure x) (hyz : z ∈ y) :
    z ∈ closure x := by
  apply (mem_closure_iff z x).mpr
  exact (Relation.ReflTransGen.single (r := fun a b : HF A => a ∈ b) hyz).trans ((mem_closure_iff y x).mp hxy)

end

end WitnessedSeparation.Hereditary

end OAI
