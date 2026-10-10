import OAI.Computability.WitnessedChoice.FormTransfer

namespace OAI


namespace WitnessedSeparation.HFCoding

noncomputable section

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

omit hd in
theorem singleton_definable : Definable S m 2 (fun v => SingletonTest (v 0) (v 1)) := by
  have hs : Definable S m 2 (fun v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 2)
  have hbody : Definable S m 3 (fun v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2) := by
    have hmem' : Definable S m 3 (fun v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 3)
    exact hmem'.iff (Definable.equal 0 2)
  exact hs.and (hbody.all (by omega))

omit hd in
theorem double_definable : Definable S m 3 (fun v => DoubleTest (v 0) (v 1) (v 2)) := by
  have hs : Definable S m 3 (fun v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 3)
  have hbody : Definable S m 4 (fun v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2 ∨ v 0 = v 3) := by
    have hmem' : Definable S m 4 (fun v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 4)
    exact hmem'.iff ((Definable.equal 0 2).or (Definable.equal 0 3))
  exact hs.and (hbody.all (by omega))

theorem pair_definable : Definable S m 3 (fun v => (v 0).val = pair (v 1).val (v 2).val) := by
  have h1 : Definable S m 5 (fun v => SingletonTest (v 1) (v 3)) := by
    simpa using (singleton_definable S hmem hset hm).reindex (![1,3] : Fin 2 → Fin 5)
  have h2 : Definable S m 5 (fun v => DoubleTest (v 0) (v 3) (v 4)) := by
    simpa using (double_definable S hmem hset hm).reindex (![0,3,4] : Fin 3 → Fin 5)
  have h3 : Definable S m 5 (fun v => DoubleTest (v 2) (v 1) (v 0)) := by
    simpa using (double_definable S hmem hset hm).reindex (![2,1,0] : Fin 3 → Fin 5)
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

end

end WitnessedSeparation.HFCoding



namespace WitnessedSeparation.Counting

noncomputable section

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

end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.HFCoding

noncomputable section

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

end

end WitnessedSeparation.HFCoding



namespace WitnessedSeparation.Interpretations

noncomputable section

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

end





noncomputable section

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





noncomputable section

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

end

end WitnessedSeparation.Interpretations



namespace WitnessedSeparation.Reachability

noncomputable section

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

end

end WitnessedSeparation.Reachability



namespace WitnessedSeparation.Counting

noncomputable section

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





noncomputable section

open Classical

variable {ι D₀ : Type*} (X : Type*) [Fintype X] (r : X → X → Prop)

variable (a b : X → D₀) (hinj : Function.Injective (fun x => (a x,b x)))

variable (L : (Fin 4 → D₀) → Prop)

variable (hL : ∀ v, L v ↔ ∃ p q, v 0 = a p ∧ v 1 = b p ∧
  v 2 = a q ∧ v 3 = b q ∧ Reachability.Link r p q)

include hinj hL

omit [Fintype X] in
theorem pairReach_lift (t : ℕ) (v : Fin 4 → D₀) :
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

end

end WitnessedSeparation.Counting

end OAI
