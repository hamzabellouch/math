import OAI.ModelTheory.Categoricity.Model

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TaggedCollapse

variable {Q : Type u} (R : Q → Q → Prop) (wf : WellFounded R)

def collapse (x : Q) : ZFSet.{u} :=
  wf.fix (fun x rec => ZFSet.range (fun y : {y // R y x} => rec y.val y.property)) x

theorem collapse_eq (x : Q) :
    collapse R wf x = ZFSet.range (fun y : {y // R y x} => collapse R wf y.val) := by
  exact wf.fix_eq _ x

theorem mem_collapse {x : Q} {z : ZFSet.{u}} :
    z ∈ collapse R wf x ↔ ∃ y, R y x ∧ collapse R wf y = z := by
  rw [collapse_eq]
  simp only [ZFSet.mem_range, Subtype.exists, exists_prop]

theorem injective
    (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y) :
    Function.Injective (collapse R wf) := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro x' heq
    apply extensional x x'
    intro y
    constructor
    · intro hy
      have hm : collapse R wf y ∈ collapse R wf x :=
        (mem_collapse R wf).2 ⟨y, hy, rfl⟩
      rw [heq] at hm
      obtain ⟨y', hy', hh⟩ := (mem_collapse R wf).1 hm
      have : y = y' := ih y hy hh.symm
      simpa only [this] using hy'
    · intro hy'
      have hm : collapse R wf y ∈ collapse R wf x' :=
        (mem_collapse R wf).2 ⟨y, hy', rfl⟩
      rw [← heq] at hm
      obtain ⟨y', hy, hh⟩ := (mem_collapse R wf).1 hm
      have : y' = y := ih y' hy hh
      simpa only [← this] using hy

theorem rank_le (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) (x : Q) :
    ZFSet.rank (collapse R wf x) ≤ ρ x := by
  induction x using wf.induction with
  | h x ih =>
    rw [collapse_eq, ZFSet.rank_range]
    apply Ordinal.iSup_le
    intro y
    exact Order.succ_le_of_lt ((ih y.val y.property).trans_lt (decreases y.property))

def embedding (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y)
    (ρ : Q → Ordinal.{u}) (decreases : ∀ {x y}, R y x → ρ y < ρ x)
    (δ : Ordinal.{u}) (bounded : ∀ x, ρ x < δ) :
    Q ↪ (ZFSet.vonNeumann δ) where
  toFun x := ⟨collapse R wf x,
    ZFSet.mem_vonNeumann.2 ((rank_le R wf ρ decreases x).trans_lt (bounded x))⟩
  inj' _x _y h := injective R wf extensional (congrArg Subtype.val h)

theorem wellFounded_of_tags (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) : WellFounded R :=
  (InvImage.wf ρ Ordinal.lt_wf).mono (fun _ _ h => decreases h)

end TaggedCollapse

namespace Domination

abbrev Alpha := {a : Ordinal.{u} // a < ω_ 2}
abbrev Beta := {b : Ordinal.{u} // b < ω_ 1}

def indexEmbedding (a : Alpha.{u}) : Set.Iio a.val ↪ Beta.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  change #(Set.Iio a.val) ≤ #(Set.Iio (ω_ (1 : Ordinal.{u})))
  rw [Cardinal.mk_Iio_ordinal, Cardinal.mk_Iio_ordinal, Cardinal.lift_le]
  have h : a.val.card < ℵ_ (2 : Ordinal.{u}) :=
    Cardinal.lt_omega_iff_card_lt.1 a.property
  have hs : ℵ_ (2 : Ordinal.{u}) = succ (ℵ_ (1 : Ordinal.{u})) := by
    rw [Cardinal.succ_aleph]
    norm_num
  simpa only [Ordinal.card_omega] using (Order.lt_succ_iff.1 (h.trans_eq hs))

theorem countable_Iio {b : Ordinal.{u}} (hb : b < ω_ 1) : Countable (Set.Iio b) := by
  apply Cardinal.mk_le_aleph0_iff.1
  rw [Cardinal.mk_Iio_ordinal, ← Cardinal.lift_aleph0.{u+1,u}, Cardinal.lift_le]
  exact Cardinal.lt_aleph_one_iff.1 (Cardinal.lt_omega_iff_card_lt.1 hb)

def Prior (a : Alpha.{u}) (b : Beta.{u}) :=
  {g : Set.Iio a.val // (indexEmbedding a g).val < b.val}

instance prior_countable (a : Alpha.{u}) (b : Beta.{u}) : Countable (Prior a b) := by
  have := countable_Iio b.property
  let f : Prior a b → Set.Iio b.val := fun g => ⟨(indexEmbedding a g.val).val, g.property⟩
  apply Function.Injective.countable (f := f)
  intro g h heq
  apply Subtype.ext
  apply (indexEmbedding a).injective
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio b.val => x.val) heq

def values (a : Alpha.{u}) : Beta.{u} → Beta.{u} :=
  (InvImage.wf (fun a : Alpha.{u} => a.val) Ordinal.lt_wf).fix
    (C := fun _ => Beta.{u} → Beta.{u})
    (fun a rec b =>
      ⟨⨆ g : Prior a b, succ (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).val,
       Ordinal.iSup_lt_omega_one (fun g =>
         (Cardinal.isSuccLimit_omega 1).succ_lt
           (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).property)⟩) a

theorem values_eq (a : Alpha.{u}) (b : Beta.{u}) :
    (values a b).val =
      ⨆ g : Prior a b, succ (values ⟨g.val.val, lt_trans g.val.property a.property⟩ b).val := by
  conv_lhs => rw [values, WellFounded.fix_eq]
  rfl

theorem eventually_lt (a : Alpha.{u}) (g : Set.Iio a.val) (b : Beta.{u})
    (hb : (indexEmbedding a g).val < b.val) :
    (values ⟨g.val, lt_trans g.property a.property⟩ b).val < (values a b).val := by
  rw [values_eq a b]
  exact (lt_succ _).trans_le (Ordinal.le_iSup _ (⟨g, hb⟩ : Prior a b))

theorem countable_exceptions (a : Alpha.{u}) (g : Set.Iio a.val) :
    {b : Beta.{u} | (values a b).val ≤ (values ⟨g.val, lt_trans g.property a.property⟩ b).val}.Countable := by
  let bound := succ (indexEmbedding a g).val
  have hb : bound < ω_ 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt (indexEmbedding a g).property
  have := countable_Iio hb
  apply Set.countable_coe_iff.1
  let f : {b : Beta.{u} | (values a b).val ≤
      (values ⟨g.val, lt_trans g.property a.property⟩ b).val} → Set.Iio bound :=
    fun b => ⟨b.val.val, Order.lt_succ_iff.2 (le_of_not_gt (fun h =>
      (eventually_lt a g b.val h).not_ge b.property))⟩
  apply Function.Injective.countable (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio bound => x.val) h

end Domination

namespace CountableClosures

variable {A : Type u} (R : A → A → Prop)
  (separates : ∀ a b, a ≠ b → ∃ w, ¬ (R w a ↔ R w b))

def witness (a b : A) : A := by
  classical
  exact if h : a = b then a else Classical.choose (separates a b h)

theorem witness_distinguishes {a b : A} (h : a ≠ b) :
    ¬ (R (witness R separates a b) a ↔ R (witness R separates a b) b) := by
  simpa only [witness, dite_eq_right h] using Classical.choose_spec (separates a b h)

def stage (S : Set A) : ℕ → Set A
  | 0 => S
  | n + 1 => stage S n ∪ Set.image2 (witness R separates) (stage S n) (stage S n)

def closure (S : Set A) : Set A := ⋃ n, stage R separates S n

theorem stage_mono (S : Set A) : Monotone (stage R separates S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

theorem subset_closure (S : Set A) : S ⊆ closure R separates S :=
  fun _ hx => Set.mem_iUnion.2 ⟨0, hx⟩

theorem closure_mono : Monotone (closure R separates) := by
  intro S T hST x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  apply Set.mem_iUnion.2 ⟨n, ?_⟩
  suffices stage R separates S n ⊆ stage R separates T n from this hn
  clear hn
  induction n with
  | zero => exact hST
  | succ n ih =>
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · rcases hy with ⟨a, ha, b, hb, rfl⟩
      exact Or.inr ⟨a, ih ha, b, ih hb, rfl⟩

theorem closure_countable {S : Set A} (hS : S.Countable) :
    (closure R separates S).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.union (ih.image2 ih _)

theorem witness_mem {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S) :
    witness R separates a b ∈ closure R separates S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
  apply Set.mem_iUnion.2 ⟨max m n + 1, ?_⟩
  exact Or.inr ⟨a, stage_mono R separates S (le_max_left _ _) hm,
    b, stage_mono R separates S (le_max_right _ _) hn, rfl⟩

theorem extensional {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S)
    (heq : ∀ w ∈ closure R separates S, R w a ↔ R w b) : a = b := by
  by_contra h
  exact witness_distinguishes R separates h (heq _ (witness_mem R separates ha hb))

abbrev FiniteSeed (A : Type u) := {X : Finset A // X.Nonempty}

def entries (X : FiniteSeed A) : Set A := closure R separates X.val

theorem entries_countable (X : FiniteSeed A) : (entries R separates X).Countable :=
  closure_countable R separates X.val.countable_toSet

theorem seed_subset (X : FiniteSeed A) : (X.val : Set A) ⊆ entries R separates X :=
  subset_closure R separates X.val

theorem entries_nonempty (X : FiniteSeed A) : (entries R separates X).Nonempty :=
  X.property.to_set.mono (seed_subset R separates X)

theorem entries_mono (X Y : FiniteSeed A) (h : X.val ⊆ Y.val) :
    entries R separates X ⊆ entries R separates Y :=
  closure_mono R separates h

def enumeration (X : FiniteSeed A) : ℕ → entries R separates X :=
  let first : entries R separates X :=
    ⟨Classical.choose X.property, seed_subset R separates X (Classical.choose_spec X.property)⟩
  let e : ℕ → entries R separates X :=
    Classical.choose (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X))
  fun n => match n with | 0 => first | n + 1 => e n

theorem enumeration_surjective (X : FiniteSeed A) :
    Function.Surjective (enumeration R separates X) := by
  intro x
  obtain ⟨n, hn⟩ := Classical.choose_spec
    (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X)) x
  exact ⟨n + 1, hn⟩

theorem enumeration_singleton (x : A) :
    (enumeration R separates ⟨{x}, Finset.singleton_nonempty x⟩ 0).val = x := by
  exact Finset.mem_singleton.1 (Classical.choose_spec (Finset.singleton_nonempty x))

theorem membership_separates (D : ZFSet.{u}) (hD : D.IsTransitive) :
    ∀ a b : D, a ≠ b → ∃ w : D, ¬ (w.val ∈ a.val ↔ w.val ∈ b.val) := by
  intro a b h
  have hab : a.val ≠ b.val := fun heq => h (Subtype.ext heq)
  obtain ⟨w, hw⟩ : ∃ w, ¬ (w ∈ a.val ↔ w ∈ b.val) := by
    by_contra hn
    exact hab (ZFSet.ext (by simpa only [not_exists, not_not] using hn))
  have hwD : w ∈ D := by
    by_cases hwa : w ∈ a.val
    · exact hD a.val a.property hwa
    · have hwb : w ∈ b.val := by tauto
      exact hD b.val b.property hwb
  exact ⟨⟨w, hwD⟩, hw⟩

end CountableClosures

namespace TaggedLimit

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  (F : ι → Type u) (f : ∀ i j, i ≤ j → F i ↪ F j)
  [DirectedSystem F (fun i j h => f i j h)]
  (R : ∀ i, F i → F i → Prop)
  (respect : ∀ i j h x y, R i x y ↔ R j (f i j h x) (f i j h y))
  (ρ : ∀ i, F i → Ordinal.{u})
  (tags : ∀ i j h x, ρ i x = ρ j (f i j h x))

def relation : DirectLimit F f → DirectLimit F f → Prop :=
  DirectLimit.lift₂ f f R (fun i j h x y => propext (respect i j h x y))

def rankTag : DirectLimit F f → Ordinal.{u} :=
  DirectLimit.lift f ρ tags

theorem relation_mk (i) (x y : F i) :
    relation F f R respect ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ ↔ R i x y := by
  rw [relation, DirectLimit.lift₂_def]

theorem rankTag_mk (i) (x : F i) :
    rankTag F f ρ tags ⟦⟨i, x⟩⟧ = ρ i x := rfl

theorem extensional (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y) :
    ∀ x y, (∀ z, relation F f R respect z x ↔ relation F f R respect z y) → x = y := by
  intro x y h
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  congr 1
  congr 1
  apply hext i a b
  intro z
  exact (relation_mk F f R respect i z a).symm.trans
    ((h ⟦⟨i, z⟩⟧).trans (relation_mk F f R respect i z b))

theorem decreases (hdec : ∀ i x y, R i y x → ρ i y < ρ i x) :
    ∀ {x y}, relation F f R respect y x → rankTag F f ρ tags y < rankTag F f ρ tags x := by
  intro x y
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  rw [relation_mk, rankTag_mk, rankTag_mk]
  exact hdec i a b

def embedding
    (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y)
    (hdec : ∀ i x y, R i y x → ρ i y < ρ i x)
    (δ : Ordinal.{u}) (hbound : ∀ i x, ρ i x < δ) :
    DirectLimit F f ↪ ZFSet.vonNeumann δ := by
  let rel := relation F f R respect
  let tag := rankTag F f ρ tags
  have hd : ∀ {x y}, rel y x → tag y < tag x := decreases F f R respect ρ tags hdec
  apply TaggedCollapse.embedding rel (TaggedCollapse.wellFounded_of_tags rel tag hd)
      (extensional F f R respect hext) tag hd δ
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk f x
  exact hbound i a

end TaggedLimit

end CHObstruction

end

end OAI
