import OAI.ModelTheory.Choiceless.Operational

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

local instance {A : Type*} : DecidableEq (HF A) := Classical.decEq _

variable {ι R : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

omit ι A d hd in
lemma member_count_iff
    {ι : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i) (i : ι) (x : Domain (d i)) (n : ℕ) :
    Nonempty ({y : Domain (d i) // y.val ∈ x.val} ≃ Fin n) ↔ (elements x.val).card = n := by
  let e : {y : Domain (d i) // y.val ∈ x.val} ≃ {y // y ∈ elements x.val} :=
    { toFun := fun y => ⟨y.val.val,y.property⟩
      invFun := fun y => ⟨⟨y.val,hd i _ x.property _ y.property⟩,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    let f := (Fintype.equivFin {y // y ∈ elements x.val}).trans (finCongr (by simpa using h))
    exact ⟨e.trans f⟩

include hd hmem hset hm

omit ι R A d S m hd hmem hset hm in
lemma uniform_double_value
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 3
    (fun _ v => (v 0).val = double (v 1).val (v 2).val) :=
  (HFCoding.uniform_double S hmem hset hm).congr
    (fun i v => HFCoding.doubleTest_iff (hd i) (v 0) (v 1) (v 2))

omit ι R A d S m hd hmem hset hm in
lemma uniform_singleton_value
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = Hereditary.singleton (v 1).val) :=
  (HFCoding.uniform_singleton S hmem hset hm).congr
    (fun i v => HFCoding.singletonTest_iff (hd i) (v 0) (v 1))

include ha in
lemma uniform_atoms : UniformDefinable S m 1 (fun i v => (v 0).val = (allAtoms : HF (A i))) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = false) := by
    apply (hset.reindex (![0] : Fin 1 → Fin 2)).neg.congr
    intro i v; dsimp; cases isSet (v 0).val <;> simp
  have hbody := (hmem.iff hs).all (by omega : 1 < m)
  apply (hset.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ isSet y.val = false) ↔ _
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    simp only [mem_ofFinset,mem_image,mem_univ,true_and]
    constructor
    · intro hy
      have ht := (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
      change isSet y = false at ht
      rcases atom_or_set y with ⟨a,rfl⟩ | he
      · exact ⟨a,rfl⟩
      · rw [he,isSet_ofFinset] at ht; contradiction
    · rintro ⟨a,rfl⟩
      exact (h ⟨atom a,ha i a⟩).mpr rfl
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y
      rw [he]
      simp only [allAtoms,mem_ofFinset,mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨a,he⟩; rw [← he]; rfl
      · intro ht
        rcases atom_or_set y.val with ⟨a,he⟩ | he
        · exact ⟨a,he.symm⟩
        · rw [he,isSet_ofFinset] at ht; contradiction

omit ι R A d S m hd hmem hset hm in
lemma uniform_union
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = unionHF (v 1).val) := by
  have hz : UniformDefinable S m 4
      (fun _ v => (v 0).val ∈ (v 3).val ∧ (v 1).val ∈ (v 0).val) :=
    (hmem.reindex (![0,3] : Fin 2 → Fin 4)).and (hmem.reindex (![1,0] : Fin 2 → Fin 4))
  have hleft : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) :=
    hmem.reindex (![0,1] : Fin 2 → Fin 3)
  have hbody := (hleft.iff (hz.ex (by omega))).all (by omega : 2 < m)
  have hset' := hset.reindex (![0] : Fin 1 → Fin 2)
  apply (hset'.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y.val ∈ z.val) ↔ _
  have hmemu (y : HF (A i)) : y ∈ unionHF (v 1).val ↔
      ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y ∈ z.val := by
    simp only [unionHF,mem_ofFinset,mem_biUnion]
    constructor
    · rintro ⟨z,hz,hy⟩
      exact ⟨⟨z,hd i _ (v 1).property _ hz⟩,hz,hy⟩
    · rintro ⟨z,hz,hy⟩; exact ⟨z.val,hz,hy⟩
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    change y ∈ (v 0).val ↔ y ∈ unionHF (v 1).val
    rw [hmemu]
    constructor
    · intro hy; exact (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
    · rintro ⟨z,hz,hy⟩
      exact (h ⟨y,hd i _ z.property _ hy⟩).mpr ⟨z,hz,hy⟩
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y; rw [he,hmemu]

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_unique
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) : UniformDefinable S m 2
    (fun _ v => (v 0).val = uniqueHF (v 1).val) := by
  have hsing := uniform_singleton_value d S hd hmem hset hm
  have hyes := hsing.reindex (![1,0] : Fin 2 → Fin 2)
  have hex : UniformDefinable S m 2 (fun i v => ∃ z : Domain (d i),
      (v 1).val = Hereditary.singleton z.val) := by
    apply ((hsing.reindex (![2,0] : Fin 2 → Fin 3)).ex (by omega)).congr
    intro i v
    apply exists_congr
    intro z
    rfl
  have hempt := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (![0] : Fin 1 → Fin 2)
  apply (hyes.or (hempt.and hex.neg)).congr
  intro i v
  change ((v 1).val = Hereditary.singleton (v 0).val ∨
    ((v 0).val = empty ∧ ¬ ∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val)) ↔ _
  have hs (z : HF (A i)) : (v 1).val = Hereditary.singleton z ↔ elements (v 1).val = {z} := by
    constructor
    · intro h; rw [h]; exact elements_ofFinset _
    · intro h
      rcases atom_or_set (v 1).val with ⟨a,he⟩ | he
      · rw [he,elements_atom] at h
        exact False.elim (by simpa using congrArg Finset.card h)
      · rw [he,h]; rfl
  have hexi : (∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val) ↔
      ∃ z, elements (v 1).val = {z} := by
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.val,(hs _).mp hz⟩
    · rintro ⟨z,hz⟩
      exact ⟨⟨z,hd i _ (v 1).property _ (by change z ∈ elements (v 1).val; rw [hz]; simp)⟩,(hs z).mpr hz⟩
  rw [hs,hexi]
  rcases uniqueHF_spec (v 1).val with ⟨z,hz,he⟩ | ⟨hne,he⟩
  · rw [he,hz]
    simp only [Finset.singleton_inj,exists_eq',not_true_eq_false,and_false,or_false]
    exact eq_comm
  · rw [he]
    constructor
    · rintro (h | ⟨h,_⟩)
      · exact False.elim (hne ⟨_,h⟩)
      · exact h
    · intro h; exact Or.inr ⟨h,hne⟩

def BoundedCard (K : ℕ) {i : ι} (z x : Domain (d i)) : Prop :=
  (elements x.val).card ≤ K ∧ z.val = cardinalityHF x.val

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_card
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) (K : ℕ) : UniformDefinable S m 2
    (fun _ v => BoundedCard d K (v 0) (v 1)) := by
  have hmemb : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 2).val) :=
    hmem.reindex (![0,2] : Fin 2 → Fin 3)
  have hdis : UniformDefinable S m 2 (fun i v => ∃ n ∈ range (K+1),
      Nonempty ({y : Domain (d i) // y.val ∈ (v 1).val} ≃ Fin n) ∧ (v 0).val = ordinal n) := by
    apply UniformDefinable.exists_finset
    intro n hn
    have hc := hmemb.exact (by omega) n
    have ho := (HFCoding.uniform_ordinal S hmem hset hm hd hp n).reindex (![0] : Fin 1 → Fin 2)
    exact hc.and ho
  apply hdis.congr
  intro i v
  simp only [member_count_iff d hd,mem_range,BoundedCard,cardinalityHF]
  constructor
  · rintro ⟨n,hn,hc,he⟩; exact ⟨by omega,by rwa [hc]⟩
  · rintro ⟨hc,he⟩; exact ⟨_,by omega,rfl,he⟩

omit ι R A d S m hd hp hmem hset hm in
lemma uniform_boolean
    {ι : Type}
    {R : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure R (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (hm : 6 ≤ m) {n : ℕ} {P : ∀ i, (Fin (n+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable S m (n+1) P) :
    UniformDefinable S m (n+1) (fun i v => (v 0).val = boolean (P i v)) := by
  have ht := (HFCoding.uniform_ordinal S hmem hset hm hd hp 1).reindex (![0] : Fin 1 → Fin (n+1))
  have hf := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (![0] : Fin 1 → Fin (n+1))
  apply ((ht.and hP).or (hf.and hP.neg)).congr
  intro i v
  change ((v 0).val = truth ∧ P i v ∨ (v 0).val = empty ∧ ¬ P i v) ↔ _
  by_cases hh : P i v <;> simp [boolean,hh]

end CPTSeparation.Operational

namespace CPTSeparation.Counting.UniformDefinable

open Classical Finset

variable {ι R : Type} {D : ι → Type} {S : ∀ i, Structure R (D i)} {m n r : ℕ}

lemma forall_finset {X : Type} {P : X → ∀ i, (Fin n → D i) → Prop} (t : Finset X)
    (h : ∀ a ∈ t, UniformDefinable S m n (P a)) :
    UniformDefinable S m n (fun i v => ∀ a ∈ t, P a i v) := by
  apply (exists_finset t (fun a ha => (h a ha).neg)).neg.congr
  intro i v; simp

lemma forall_finite {X : Type} [Fintype X] {P : X → ∀ i, (Fin n → D i) → Prop}
    (h : ∀ a, UniformDefinable S m n (P a)) :
    UniformDefinable S m n (fun i v => ∀ a, P a i v) := by
  simpa only [Finset.mem_univ,true_implies] using forall_finset univ (fun a _ => h a)

lemma append_cons {X : Type} (x : X) (u : Fin r → X) (v : Fin n → X) :
    Fin.append (Fin.cons x u) v = Fin.cons x (Fin.append u v) ∘
      (finCongr (by omega : (r+1)+n = r+n+1)) := by
  rw [Fin.append_cons]
  congr 1

lemma exists_vec {P : ∀ i, (Fin (r+n) → D i) → Prop}
    (h : UniformDefinable S m (r+n) P) (hroom : r+n ≤ m) :
    UniformDefinable S m n (fun i v => ∃ u : Fin r → D i, P i (Fin.append u v)) := by
  induction r with
  | zero =>
    have h' := h.reindex (finCongr (Nat.zero_add n))
    apply h'.congr
    intro i v
    have he (u : Fin 0 → D i) : Fin.append u v = v ∘ finCongr (Nat.zero_add n) := by
      rw [Fin.append_left_nil u v rfl]
      congr 1
    constructor
    · intro hp; exact ⟨Fin.elim0,by rw [he]; exact hp⟩
    · rintro ⟨u,hp⟩; rwa [he] at hp
  | succ r ih =>
    have h' := h.reindex (finCongr (by omega : (r+1)+n = (r+n)+1))
    have he := h'.ex (by omega)
    have hi := ih he (by omega)
    apply hi.congr
    intro i v
    constructor
    · rintro ⟨u,x,hp⟩
      exact ⟨Fin.cons x u,by simpa only [append_cons] using hp⟩
    · rintro ⟨u,hp⟩
      refine ⟨Fin.tail u,u 0,?_⟩
      simpa only [← append_cons,Fin.cons_self_tail] using hp

lemma compose_unary {P : ∀ i, (Fin (n+1) → D i) → Prop}
    {Q : ∀ i, (Fin 2 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m 2 Q)
    (hr : n+1 < m) : UniformDefinable S m (n+1)
      (fun i v => ∃ x, P i (Fin.cons x (Fin.tail v)) ∧ Q i ![v 0,x]) := by
  have h1 := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h2 := hQ.reindex (![1,0] : Fin 2 → Fin (n+2))
  apply ((h1.and h2).ex hr).congr
  intro i v
  apply exists_congr; intro x
  have he : Fin.cons x v ∘ (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) =
      Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons x v ∘ (![1,0] : Fin 2 → Fin (n+2)) = ![v 0,x] := by
    funext j; fin_cases j <;> rfl
  simp only [he,he2]

lemma compose_binary {P Q : ∀ i, (Fin (n+1) → D i) → Prop}
    {T : ∀ i, (Fin 3 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q)
    (hT : UniformDefinable S m 3 T) (hr : n+2 < m) :
    UniformDefinable S m (n+1) (fun i v => ∃ x y,
      P i (Fin.cons x (Fin.tail v)) ∧ Q i (Fin.cons y (Fin.tail v)) ∧ T i ![v 0,x,y]) := by
  have h1 := hP.reindex (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h2 := hQ.reindex (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h3 := hT.reindex (![2,1,0] : Fin 3 → Fin (n+3))
  apply (((h1.and (h2.and h3)).ex hr).ex (by omega)).congr
  intro i v
  apply exists_congr; intro x
  apply exists_congr; intro y
  have he1 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons y (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he3 : Fin.cons y (Fin.cons x v) ∘ (![2,1,0] : Fin 3 → Fin (n+3)) = ![v 0,x,y] := by
    funext j; fin_cases j <;> rfl
  simp only [he1,he2,he3]

lemma compose_vec {P : Fin r → ∀ i, (Fin (n+1) → D i) → Prop}
    {Q : ∀ i, (Fin (r+1) → D i) → Prop}
    (hP : ∀ j, UniformDefinable S m (n+1) (P j)) (hQ : UniformDefinable S m (r+1) Q)
    (hr : r+(n+1) ≤ m) : UniformDefinable S m (n+1)
      (fun i v => ∃ w : Fin r → D i,
        (∀ j, P j i (Fin.cons (w j) (Fin.tail v))) ∧ Q i (Fin.cons (v 0) w)) := by
  let ix (j : Fin r) : Fin (n+1) → Fin (r+(n+1)) :=
    Fin.cons (j.castAdd (n+1)) (fun l => l.succ.natAdd r)
  let iq : Fin (r+1) → Fin (r+(n+1)) :=
    Fin.cons ((0 : Fin (n+1)).natAdd r) (fun j => j.castAdd (n+1))
  have h1 := forall_finite (fun j => (hP j).reindex (ix j))
  have h2 := hQ.reindex iq
  apply ((h1.and h2).exists_vec hr).congr
  intro i v
  apply exists_congr
  intro w
  have he1 (j : Fin r) : Fin.append w v ∘ ix j = Fin.cons (w j) (Fin.tail v) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  have he2 : Fin.append w v ∘ iq = Fin.cons (v 0) w := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact Fin.append_right _ _ _
    · exact Fin.append_left _ _ _
  simp only [he1,he2]

end CPTSeparation.Counting.UniformDefinable

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

local instance {A : Type*} : DecidableEq (HF A) := Classical.decEq _

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

def Graph (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → Domain d → (Fin k → Domain d) → Prop
  | _,.var j,z,v => z = v j
  | _,.constant n,z,_ => z.val = ordinal n
  | _,.atoms,z,_ => z.val = allAtoms
  | _,.app f args,z,v => ∃ w : Fin (arity f) → Domain d,
      (∀ j, Graph d K rel s (args j) (w j) v) ∧ z.val = s.value ⟨f,fun j => (w j).val⟩
  | _,.pair a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = double x.val y.val
  | _,.union a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = unionHF x.val
  | _,.unique a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = uniqueHF x.val
  | _,.card a,z,v => ∃ x, Graph d K rel s a x v ∧ (elements x.val).card ≤ K ∧ z.val = cardinalityHF x.val
  | _,.equal a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val = y.val)
  | _,.member a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val ∈ y.val)
  | _,.isAtom a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = boolean (isSet x.val = false)
  | _,.input r a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (inputRelation rel r x.val y.val)
  | _,.not a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = boolean (x.val ≠ truth)
  | _,.and a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val = truth ∧ y.val = truth)
  | _,.conditional c a b,z,v => ∃ x, Graph d K rel s c x v ∧
      ((x.val = truth ∧ Graph d K rel s a z v) ∨ (x.val ≠ truth ∧ Graph d K rel s b z v))
  | _,.comprehension bound guard body,z,v => ∃ b, Graph d K rel s bound b v ∧
      (∀ x : Domain d, x.val ∈ b.val → ∃ g y, Graph d K rel s guard g (Fin.cons x v) ∧ Graph d K rel s body y (Fin.cons x v)) ∧
      isSet z.val = true ∧ ∀ y : Domain d, y.val ∈ z.val ↔ ∃ x : Domain d,
        x.val ∈ b.val ∧ (∃ g, Graph d K rel s guard g (Fin.cons x v) ∧ g.val = truth) ∧
        Graph d K rel s body y (Fin.cons x v)

variable (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A)

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

include hd in
lemma graph_sound {k : ℕ} (t : Term R F arity k) (z : Domain d) (v : Fin k → Domain d)
    (h : Graph d K rel s t z v) : z.val = t.eval rel s (fun j => (v j).val) := by
  induction t generalizing z with
  | var j => exact congrArg Subtype.val h
  | constant n => exact h
  | atoms => exact h
  | app f args ih =>
    obtain ⟨w,hw,hz⟩ := h
    have he : (fun j => (w j).val) = fun j => (args j).eval rel s (fun j => (v j).val) := funext (fun j => ih j _ _ (hw j))
    simpa only [eval,he] using hz
  | pair a b iha ihb | equal a b iha ihb | member a b iha ihb | input r a b iha ihb | and a b iha ihb =>
    obtain ⟨x,y,hx,hy,hz⟩ := h
    simpa only [eval,iha _ _ hx,ihb _ _ hy] using hz
  | union a ih | unique a ih | isAtom a ih | not a ih =>
    obtain ⟨x,hx,hz⟩ := h
    simpa only [eval,ih _ _ hx] using hz
  | card a ih =>
    obtain ⟨x,hx,_,hz⟩ := h
    simpa only [eval,ih _ _ hx] using hz
  | conditional c a b ihc iha ihb =>
    obtain ⟨x,hx,h⟩ := h
    have he := ihc _ _ hx
    rcases h with ⟨ht,h⟩ | ⟨ht,h⟩
    · simpa only [eval,← he,ite_eq_left ht] using iha _ _ h
    · simpa only [eval,← he,ite_eq_right ht] using ihb _ _ h
  | @comprehension k bound guard body ihb ihg ihy =>
    obtain ⟨b,hb,hall,hz,hmem⟩ := h
    have heb := ihb _ _ hb
    apply ext_sets hz (isSet_ofFinset _)
    intro y

    simp only [mem_ofFinset,mem_image,mem_filter]
    have hc (x : Domain d) : (fun j : Fin (k+1) => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    constructor
    · intro hy
      obtain ⟨x,hxb,⟨g,hg,hgt⟩,hyb⟩ := (hmem ⟨y,hd _ z.property _ hy⟩).mp hy
      refine ⟨x.val,⟨by rwa [← heb],?_⟩,?_⟩
      · rw [← hc x,← ihg _ _ hg]; exact hgt
      · have he : y = body.eval rel s (Fin.cons x.val (fun j => (v j).val)) := by
          simpa only [hc] using ihy _ _ hyb
        exact he.symm
    · rintro ⟨x,⟨hxb,hgt⟩,heq⟩
      have hxd : x ∈ d := hd _ b.property _ (by rwa [heb])
      let xx : Domain d := ⟨x,hxd⟩
      obtain ⟨g,w,hg,hw⟩ := hall xx (by change x ∈ b.val; rwa [heb])
      have hgw := ihg _ _ hg
      have hyw := ihy _ _ hw
      simp only [hc] at hgw hyw
      have hyw' : w.val = y := hyw.trans heq
      have hyd : y ∈ d := hyw' ▸ w.property
      apply (hmem ⟨y,hyd⟩).mpr
      refine ⟨xx,by change x ∈ b.val; rwa [heb],⟨g,hg,?_⟩,?_⟩
      · exact hgw.trans hgt
      · have he : w = (⟨y,hyd⟩ : Domain d) := Subtype.ext hyw'
        rwa [← he]

lemma eval_mem_trace {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.eval rel s v ∈ t.trace rel s v :=
  closure_eval_subset_trace rel s t v (mem_closure_self _)

include hd in
lemma graph_complete {k : ℕ} (t : Term R F arity k) (v : Fin k → Domain d)
    (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :
    ∃ z : Domain d, Graph d K rel s t z v ∧ z.val = t.eval rel s (fun j => (v j).val) := by
  have result {k : ℕ} (t : Term R F arity k) (v : Fin k → Domain d)
      (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :
      t.eval rel s (fun j => (v j).val) ∈ d := (ht _ (eval_mem_trace rel s t _)).1
  induction t with
  | var j => exact ⟨v j,rfl,rfl⟩
  | constant n => exact ⟨⟨ordinal n,result _ _ ht⟩,rfl,rfl⟩
  | atoms => exact ⟨⟨allAtoms,result _ _ ht⟩,rfl,rfl⟩
  | app f args ih =>
    have hall : ∀ j, ∃ x : Domain d, Graph d K rel s (args j) x v ∧
        x.val = (args j).eval rel s (fun j => (v j).val) := by
      intro j
      apply ih j
      intro x hx
      apply ht x
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hx⟩)
    choose w hw using hall
    refine ⟨⟨_,result _ _ ht⟩,⟨w,fun j => (hw j).1,?_⟩,rfl⟩
    change s.value _ = s.value _
    congr 1
    exact Sigma.ext rfl (heq_of_eq (funext (fun j => (hw j).2.symm)))
  | pair a b iha ihb | equal a b iha ihb | member a b iha ihb | input r a b iha ihb | and a b iha ihb =>
    obtain ⟨x,hx,hex⟩ := iha v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    obtain ⟨y,hy,hey⟩ := ihb v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,y,hx,hy,?_⟩,rfl⟩
    simp only [eval,hex,hey]
  | union a ih | unique a ih | isAtom a ih | not a ih =>
    obtain ⟨x,hx,hex⟩ := ih v (by
      intro x hx; apply ht x; exact mem_union_right _ hx)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,hx,?_⟩,rfl⟩
    simp only [eval,hex]
  | card a ih =>
    obtain ⟨x,hx,hex⟩ := ih v (by
      intro x hx; apply ht x; exact mem_union_right _ hx)
    refine ⟨⟨_,result _ _ ht⟩,⟨x,hx,?_,?_⟩,rfl⟩
    · rw [hex]; exact (ht _ (mem_union_right _ (eval_mem_trace rel s a _))).2
    · simp only [eval,hex]
  | conditional c a b ihc iha ihb =>
    obtain ⟨x,hx,hex⟩ := ihc v (by
      intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
    by_cases hc : x.val = truth
    · obtain ⟨z,hz,hez⟩ := iha v (by
        intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
      refine ⟨z,⟨x,hx,Or.inl ⟨hc,hz⟩⟩,?_⟩
      simpa only [eval,← hex,ite_eq_left hc] using hez
    · obtain ⟨z,hz,hez⟩ := ihb v (by
        intro x hx; apply ht x; simp only [trace,mem_union]; tauto)
      refine ⟨z,⟨x,hx,Or.inr ⟨hc,hz⟩⟩,?_⟩
      simpa only [eval,← hex,ite_eq_right hc] using hez
  | @comprehension k bound guard body ihb ihg ihy =>
    obtain ⟨b,hb,heb⟩ := ihb v (by
      intro x hx; apply ht x; exact mem_insert_of_mem (mem_union_left _ hx))
    have hc (x : Domain d) : (fun j : Fin (k+1) => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) =
        Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    have hall (x : Domain d) (hxb : x.val ∈ b.val) :
        (∃ g, Graph d K rel s guard g (Fin.cons x v) ∧ g.val = guard.eval rel s (Fin.cons x.val (fun j => (v j).val))) ∧
        (∃ y, Graph d K rel s body y (Fin.cons x v) ∧ y.val = body.eval rel s (Fin.cons x.val (fun j => (v j).val))) := by
      constructor
      · have hh := ihg (Fin.cons x v) (by
          intro y hy; apply ht y
          apply mem_insert_of_mem
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨x.val,by rwa [← heb],?_⟩
          apply mem_union_left
          simpa only [hc] using hy)
        simpa only [hc] using hh
      · have hh := ihy (Fin.cons x v) (by
          intro y hy; apply ht y
          apply mem_insert_of_mem
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨x.val,by rwa [← heb],?_⟩
          apply mem_union_right
          simpa only [hc] using hy)
        simpa only [hc] using hh
    let z : Domain d := ⟨_,result _ _ ht⟩
    refine ⟨z,⟨b,hb,?_,isSet_ofFinset _,?_⟩,rfl⟩
    · intro x hx
      obtain ⟨⟨g,hg,_⟩,⟨y,hy,_⟩⟩ := hall x hx
      exact ⟨g,y,hg,hy⟩
    · intro y
      change y.val ∈ ofFinset _ ↔ _
      simp only [mem_ofFinset,mem_image,mem_filter]
      constructor
      · rintro ⟨x,⟨hx,htrue⟩,hy⟩
        have hxd : x ∈ d := (ht _ (mem_insert_of_mem (mem_union_left _
          (closure_eval_subset_trace rel s bound _ (elements_subset_closure _ hx))))).1
        let xx : Domain d := ⟨x,hxd⟩
        have hxb : xx.val ∈ b.val := by change x ∈ b.val; rwa [heb]
        obtain ⟨⟨g,hg,heg⟩,⟨w,hw,hew⟩⟩ := hall xx hxb
        refine ⟨xx,hxb,⟨g,hg,heg.trans htrue⟩,?_⟩
        have he : w = y := Subtype.ext (hew.trans hy)
        rwa [← he]
      · rintro ⟨x,hxb,⟨g,hg,hgt⟩,hy⟩
        have heg := graph_sound d K rel s hd guard g (Fin.cons x v) hg
        have hey := graph_sound d K rel s hd body y (Fin.cons x v) hy
        simp only [hc] at heg hey
        exact ⟨x.val,⟨by rwa [← heb],heg.symm.trans hgt⟩,hey.symm⟩

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {ι R : Type} {A : ι → Type} (d : ∀ i, Set (HF (A i)))

variable (S : ∀ i, Counting.Structure R (Domain (d i))) {m k : ℕ}

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (htruth : UniformDefinable S m 1 (fun _ v => (v 0).val = truth))

include hmem hset htruth in
lemma uniform_comprehension
    {P : ∀ i, Domain (d i) → (Fin k → Domain (d i)) → Prop}
    {Q T : ∀ i, Domain (d i) → (Fin (k+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable S m (k+1) (fun i v => P i (v 0) (Fin.tail v)))
    (hQ : UniformDefinable S m (k+2) (fun i v => Q i (v 0) (Fin.tail v)))
    (hT : UniformDefinable S m (k+2) (fun i v => T i (v 0) (Fin.tail v)))
    (hm : k+5 ≤ m) : UniformDefinable S m (k+1) (fun i v => ∃ b,
      P i b (Fin.tail v) ∧
      (∀ x : Domain (d i), x.val ∈ b.val → ∃ g y,
        Q i g (Fin.cons x (Fin.tail v)) ∧ T i y (Fin.cons x (Fin.tail v))) ∧
      isSet (v 0).val = true ∧ ∀ y : Domain (d i), y.val ∈ (v 0).val ↔ ∃ x : Domain (d i),
        x.val ∈ b.val ∧ (∃ g, Q i g (Fin.cons x (Fin.tail v)) ∧ g.val = truth) ∧
        T i y (Fin.cons x (Fin.tail v))) := by
  have hQtotal := hQ.reindex (Fin.cons 1 (Fin.cons 2 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have hTtotal := hT.reindex (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have htotal := ((hmem.reindex (![0,1] : Fin 2 → Fin (k+3))).imp
    (((hQtotal.and hTtotal).ex (by omega)).ex (by omega))).all (by omega)
  have hQmember := hQ.reindex (Fin.cons 0 (Fin.cons 1 (fun j => j.succ.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+5))
  have hgtruth := htruth.reindex (![0] : Fin 1 → Fin (k+5))
  have hguard := (hQmember.and hgtruth).ex (by omega)
  have hTmember := hT.reindex (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ.succ)) : Fin (k+2) → Fin (k+4))
  have hrhs := ((hmem.reindex (![0,2] : Fin 2 → Fin (k+4))).and (hguard.and hTmember)).ex (by omega)
  have hext := ((hmem.reindex (![0,2] : Fin 2 → Fin (k+3))).iff hrhs).all (by omega)
  have hbound := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (k+1) → Fin (k+2))
  have hset' := hset.reindex (![1] : Fin 1 → Fin (k+2))
  apply ((hbound.and (htotal.and (hset'.and hext))).ex (by omega)).congr
  intro i v
  simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
  rfl

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

local instance {A : Type*} : DecidableEq (HF A) := Classical.decEq _

variable {R F : Type} {arity : F → ℕ}

def width : {k : ℕ} → Term R F arity k → ℕ
  | k,.var _ | k,.constant _ | k,.atoms => k+6
  | k,.app f args => k+6+arity f+∑ j, width (args j)
  | k,.pair a b | k,.equal a b | k,.member a b | k,.input _ a b | k,.and a b => k+6+width a+width b
  | k,.union a | k,.unique a | k,.card a | k,.isAtom a | k,.not a => k+6+width a
  | k,.conditional c a b => k+6+width c+width a+width b
  | k,.comprehension a b c => k+6+width a+width b+width c

variable {ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_graph (K : ℕ) {k : ℕ} (t : Term R F arity k) (hm : t.width ≤ m) :
    UniformDefinable S m (k+1) (fun i v => Graph (d i) K (rel i) (s i) t (v 0) (Fin.tail v)) := by
  induction t with
  | var j => exact UniformDefinable.equal 0 j.succ
  | constant n =>
    simp only [width] at hm
    exact (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp n).reindex ![0]
  | atoms =>
    simp only [width] at hm
    exact (uniform_atoms d S hd ha hmem hset (by omega)).reindex ![0]
  | @app k f args ih =>
    simp only [width] at hm
    have hh (j) := (single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (arity f)))) => Nat.zero_le (width (args j))) (mem_univ j))
    have hh' := UniformDefinable.compose_vec (fun j => ih j (by have := hh j; omega)) (hstate f) (by omega)
    simpa only [Graph,Fin.cons_zero,Fin.tail_cons,Fin.cons_succ] using hh'
  | pair a b iha ihb =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega))
      (uniform_double_value d S hd hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | union a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_union d S hd hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | unique a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_unique d S hd hp hmem hset (by omega)) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | card a ih =>
    simp only [width] at hm
    have hh := UniformDefinable.compose_unary (ih (by omega)) (uniform_card d S hd hp hmem hset (by omega) K) (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,BoundedCard,Fin.cons_zero,Fin.tail_cons]
    rfl
  | equal a b iha ihb =>
    simp only [width] at hm
    have htest : UniformDefinable S m 3 (fun _ v => (v 1).val = (v 2).val) :=
      (UniformDefinable.equal 1 2).congr (fun _ _ => Subtype.ext_iff)
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) htest
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | member a b iha ihb =>
    simp only [width] at hm
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) (hmem.reindex (![1,2] : Fin 2 → Fin 3))
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | isAtom a ih =>
    simp only [width] at hm
    have htest : UniformDefinable S m 2 (fun _ v => isSet (v 1).val = false) := by
      apply (hset.reindex (![1] : Fin 1 → Fin 2)).neg.congr
      intro i v; dsimp; cases isSet (v 1).val <;> simp
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) htest
    have hh := UniformDefinable.compose_unary (ih (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | input r a b iha ihb =>
    simp only [width] at hm
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) ((hinput r).reindex (![1,2] : Fin 2 → Fin 3))
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | not a ih =>
    simp only [width] at hm
    have ht := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![1] : Fin 1 → Fin 2)
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) ht.neg
    have hh := UniformDefinable.compose_unary (ih (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | and a b iha ihb =>
    simp only [width] at hm
    have ht := HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1
    have hpred := (ht.reindex (![1] : Fin 1 → Fin 3)).and (ht.reindex (![2] : Fin 1 → Fin 3))
    have hbool := uniform_boolean d S hd hp hmem hset (by omega) hpred
    have hh := UniformDefinable.compose_binary (iha (by omega)) (ihb (by omega)) hbool (by omega)
    apply hh.congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.tail_cons]
    rfl
  | @conditional k c a b ihc iha ihb =>
    simp only [width] at hm
    have h0 := (ihc (by omega)).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (k+1) → Fin (k+2))
    have h1 := (iha (by omega)).reindex (Fin.succ : Fin (k+1) → Fin (k+2))
    have h2 := (ihb (by omega)).reindex (Fin.succ : Fin (k+1) → Fin (k+2))
    have ht := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![0] : Fin 1 → Fin (k+2))
    apply ((h0.and ((ht.and h1).or (ht.neg.and h2))).ex (by omega)).congr
    intro i v
    simp only [Graph,Fin.cons_zero,Fin.cons_succ,Function.comp_def]
    rfl
  | comprehension bound guard body ihb ihg ihy =>
    simp only [width] at hm
    exact uniform_comprehension d S hmem hset (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1)
      (ihb (by omega)) (ihg (by omega)) (ihy (by omega)) (by omega)

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational.Rule

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

def trace (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (Fin k → HF A) → Finset (HF A)
  | _,.skip,_ => ∅
  | _,.update _ args value,v => value.trace rel s v ∪ univ.biUnion (fun j => (args j).trace rel s v)
  | _,.parallel a b,v => trace rel s a v ∪ trace rel s b v
  | _,.conditional c a b,v => c.trace rel s v ∪ trace rel s a v ∪ trace rel s b v
  | _,.forall b r,v => b.trace rel s v ∪ (elements (b.eval rel s v)).biUnion (fun x => trace rel s r (Fin.cons x v))
  | _,.letValue b r,v => b.trace rel s v ∪ trace rel s r (Fin.cons (b.eval rel s v) v)

def bound : {k : ℕ} → Rule R F arity k → Polynomial ℕ
  | _,.skip => 0
  | _,.update _ args value => value.bound + ∑ j, (args j).bound
  | _,.parallel a b => bound a + bound b
  | _,.conditional c a b => c.bound + bound a + bound b
  | _,.forall b r => b.bound + b.bound * (bound r).comp (.X + b.bound)
  | _,.letValue b r => b.bound + (bound r).comp (.X + b.bound)

lemma closure_update_subset_trace (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A)
    {l : Location F arity A} {z : HF A} (hu : (l,z) ∈ r.updates rel s v) :
    closure z ⊆ r.trace rel s v ∧ ∀ j, closure (l.2 j) ⊆ r.trace rel s v := by
  induction r generalizing l z with
  | skip => simp [updates] at hu
  | update f args value =>
    have he := mem_singleton.mp hu
    cases he
    refine ⟨(Term.closure_eval_subset_trace rel s value v).trans subset_union_left,?_⟩
    intro j x hx
    exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,Term.closure_eval_subset_trace rel s (args j) v hx⟩)
  | parallel a b ia ib =>
    rcases mem_union.mp hu with ha | hb
    · obtain ⟨hz,hl⟩ := ia v ha
      exact ⟨hz.trans subset_union_left, fun j => (hl j).trans subset_union_left⟩
    · obtain ⟨hz,hl⟩ := ib v hb
      exact ⟨hz.trans subset_union_right, fun j => (hl j).trans subset_union_right⟩
  | conditional c a b ia ib =>
    unfold updates at hu
    split at hu
    · obtain ⟨hz,hl⟩ := ia v hu
      have hs : a.trace rel s v ⊆ (conditional c a b).trace rel s v :=
        subset_union_right.trans subset_union_left
      exact ⟨hz.trans hs,fun j => (hl j).trans hs⟩
    · obtain ⟨hz,hl⟩ := ib v hu
      exact ⟨hz.trans subset_union_right,fun j => (hl j).trans subset_union_right⟩
  | «forall» b r ih =>
    obtain ⟨x,hx,hu⟩ := mem_biUnion.mp hu
    obtain ⟨hz,hl⟩ := ih _ hu
    have hs : r.trace rel s (Fin.cons x v) ⊆ (Rule.forall b r).trace rel s v := by
      intro y hy; exact mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hy⟩)
    exact ⟨hz.trans hs,fun j => (hl j).trans hs⟩
  | letValue b r ih =>
    obtain ⟨hz,hl⟩ := ih _ hu
    exact ⟨hz.trans subset_union_right,fun j => (hl j).trans subset_union_right⟩

lemma card_trace_le (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) (K : ℕ) (hK : Term.potential s v ≤ K) :
    (r.trace rel s v).card ≤ r.bound.eval K := by
  induction r generalizing K with
  | skip => simp [trace,bound]
  | update f args value =>
    have hu := (card_union_le (value.trace rel s v) (univ.biUnion (fun j => (args j).trace rel s v))).trans
      (add_le_add (Term.card_trace_le rel s value v K hK)
        (card_biUnion_le.trans (sum_le_sum (fun j hj => Term.card_trace_le rel s (args j) v K hK))))
    simpa only [trace,bound,Polynomial.eval_add,Polynomial.eval_finsetSum] using hu
  | parallel a b ia ib =>
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add] using add_le_add (ia v K hK) (ib v K hK))
  | conditional c a b ia ib =>
    exact (card_union_le _ _).trans ((add_le_add (card_union_le _ _) (le_refl _)).trans (by
      simpa only [bound,Polynomial.eval_add] using add_le_add (add_le_add (Term.card_trace_le rel s c v K hK) (ia v K hK)) (ib v K hK)))
  | «forall» b r ih =>
    have hb := Term.card_trace_le rel s b v K hK
    have hc := (card_le_card ((elements_subset_closure (b.eval rel s v)).trans (Term.closure_eval_subset_trace rel s b v))).trans hb
    have he (x) (hx : x ∈ elements (b.eval rel s v)) : Term.potential s (Fin.cons x v) ≤ K+b.bound.eval K := by
      rw [Term.potential_cons]
      exact add_le_add hK ((card_le_card ((closure_member_subset hx).trans (Term.closure_eval_subset_trace rel s b v))).trans hb)
    have hs : ((elements (b.eval rel s v)).biUnion (fun x => r.trace rel s (Fin.cons x v))).card ≤
        b.bound.eval K * r.bound.eval (K+b.bound.eval K) := by
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _x ∈ elements (b.eval rel s v), r.bound.eval (K+b.bound.eval K) := sum_le_sum (fun x hx => ih _ _ (he x hx))
        _ = (elements (b.eval rel s v)).card * r.bound.eval (K+b.bound.eval K) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X] using add_le_add hb hs)
  | letValue b r ih =>
    have hb := Term.card_trace_le rel s b v K hK
    have he : Term.potential s (Fin.cons (b.eval rel s v) v) ≤ K+b.bound.eval K := by
      rw [Term.potential_cons]
      exact add_le_add hK ((card_le_card (Term.closure_eval_subset_trace rel s b v)).trans hb)
    exact (card_union_le _ _).trans (by simpa only [bound,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X] using add_le_add hb (ih _ _ he))

end

section

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

def Graph (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (f : F) → Domain d → (Fin (arity f) → Domain d) → (Fin k → Domain d) → Prop
  | _,.skip,_,_,_,_ => False
  | _,.update g args value,f,z,a,v => if h : g = f then
      Term.Graph d K rel s value z v ∧ ∀ j, Term.Graph d K rel s (args j) (a (Fin.cast (congrArg arity h) j)) v else False
  | _,.parallel r t,f,z,a,v => Graph d K rel s r f z a v ∨ Graph d K rel s t f z a v
  | _,.conditional c r t,f,z,a,v => ∃ b, Term.Graph d K rel s c b v ∧
      ((b.val = truth ∧ Graph d K rel s r f z a v) ∨ (b.val ≠ truth ∧ Graph d K rel s t f z a v))
  | _,.forall b r,f,z,a,v => ∃ w x, Term.Graph d K rel s b w v ∧ x.val ∈ w.val ∧ Graph d K rel s r f z a (Fin.cons x v)
  | _,.letValue b r,f,z,a,v => ∃ w, Term.Graph d K rel s b w v ∧ Graph d K rel s r f z a (Fin.cons w v)

variable (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A)

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

include hd in
lemma graph_sound {k : ℕ} (r : Rule R F arity k) (f : F) (z : Domain d)
    (a : Fin (arity f) → Domain d) (v : Fin k → Domain d)
    (h : Graph d K rel s r f z a v) :
    (⟨f,fun j => (a j).val⟩,z.val) ∈ r.updates rel s (fun j => (v j).val) := by
  induction r generalizing f z a with
  | skip => exact h.elim
  | update g args value =>
    unfold Graph at h
    split at h
    next he =>
      subst g
      obtain ⟨hz,ha⟩ := h
      have hv := Term.graph_sound d K rel s hd value z v hz
      have ha' : (fun j => (a j).val) = fun j => (args j).eval rel s (fun j => (v j).val) :=
        funext (fun j => Term.graph_sound d K rel s hd (args j) (a j) v (ha j))
      simp only [updates,Finset.mem_singleton,hv,ha']
    next he => exact h.elim
  | parallel r t ir it => exact h.elim (fun h => mem_union_left _ (ir _ _ _ _ h)) (fun h => mem_union_right _ (it _ _ _ _ h))
  | conditional c r t ir it =>
    obtain ⟨b,hb,h⟩ := h
    have he := Term.graph_sound d K rel s hd c b v hb
    rcases h with ⟨hc,hr⟩ | ⟨hc,ht⟩
    · simpa only [updates,← he,ite_eq_left hc] using ir _ _ _ _ hr
    · simpa only [updates,← he,ite_eq_right hc] using it _ _ _ _ ht
  | @«forall» k b r ih =>
    obtain ⟨w,x,hw,hx,hr⟩ := h
    have he := Term.graph_sound d K rel s hd b w v hw
    refine mem_biUnion.mpr ⟨x.val,by rwa [← he],?_⟩
    have hv : (fun j => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa only [hv] using ih f z a (Fin.cons x v) hr
  | @letValue k b r ih =>
    obtain ⟨w,hw,hr⟩ := h
    have he := Term.graph_sound d K rel s hd b w v hw
    have hv : (fun j => ((Fin.cons w v : Fin (k+1) → Domain d) j).val) = Fin.cons w.val (fun j => (v j).val) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa only [updates,hv,he] using ih f z a (Fin.cons w v) hr

include hd in
lemma graph_complete {k : ℕ} (r : Rule R F arity k) (f : F) (z : Domain d)
    (a : Fin (arity f) → Domain d) (v : Fin k → Domain d)
    (ht : ∀ x ∈ r.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K)
    (hu : (⟨f,fun j => (a j).val⟩,z.val) ∈ r.updates rel s (fun j => (v j).val)) :
    Graph d K rel s r f z a v := by
  have witness {k} (t : Term R F arity k) (v : Fin k → Domain d)
      (ht : ∀ x ∈ t.trace rel s (fun j => (v j).val), x ∈ d ∧ (elements x).card ≤ K) :=
    Term.graph_complete d K rel s hd t v ht
  have hv {k} (x : Domain d) (v : Fin k → Domain d) :
      (fun j => ((Fin.cons x v : Fin (k+1) → Domain d) j).val) = Fin.cons x.val (fun j => (v j).val) := by
    funext j; refine Fin.cases rfl (fun _ => rfl) j
  induction r generalizing f z a with
  | skip => simp [updates] at hu
  | update g args value =>
    have he := Finset.mem_singleton.mp hu
    have hfg : f = g := congrArg (fun p => p.1.1) he
    subst g
    have haz := (Prod.mk.inj he)
    have ha : (fun j => (a j).val) = fun j => (args j).eval rel s (fun j => (v j).val) := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp haz.1).2
    simp only [Graph,Fin.cast_refl,id_eq]
    constructor
    · obtain ⟨w,hw,hew⟩ := witness value v (fun x hx => ht x (mem_union_left _ hx))
      have hew' : w = z := Subtype.ext (hew.trans haz.2.symm)
      rwa [← hew']
    · intro j
      obtain ⟨w,hw,hew⟩ := witness (args j) v (fun x hx => ht x (mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hx⟩)))
      have hew' : w = a j := Subtype.ext (hew.trans (congrFun ha j).symm)
      rwa [← hew']
  | parallel r t ir it =>
    rcases mem_union.mp hu with h | h
    · exact Or.inl (ir _ _ _ _ (fun x hx => ht x (mem_union_left _ hx)) h)
    · exact Or.inr (it _ _ _ _ (fun x hx => ht x (mem_union_right _ hx)) h)
  | conditional c r t ir it =>
    obtain ⟨b,hb,he⟩ := witness c v (fun x hx => ht x (mem_union_left _ (mem_union_left _ hx)))
    refine ⟨b,hb,?_⟩
    by_cases hc : b.val = truth
    · left; refine ⟨hc,ir _ _ _ _ (fun x hx => ht x (mem_union_left _ (mem_union_right _ hx))) ?_⟩
      simpa only [updates,← he,ite_eq_left hc] using hu
    · right; refine ⟨hc,it _ _ _ _ (fun x hx => ht x (mem_union_right _ hx)) ?_⟩
      simpa only [updates,← he,ite_eq_right hc] using hu
  | @«forall» k b r ih =>
    obtain ⟨w,hw,he⟩ := witness b v (fun x hx => ht x (mem_union_left _ hx))
    obtain ⟨x,hx,hu⟩ := mem_biUnion.mp hu
    have hxd : x ∈ d := hd _ w.property _ (by rwa [he])
    let xx : Domain d := ⟨x,hxd⟩
    refine ⟨w,xx,hw,by change x ∈ w.val; rwa [he],ih _ _ _ (Fin.cons xx v) ?_ ?_⟩
    · intro y hy
      rw [hv] at hy
      exact ht y (mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hy⟩))
    · simpa only [hv] using hu
  | @letValue k b r ih =>
    obtain ⟨w,hw,he⟩ := witness b v (fun x hx => ht x (mem_union_left _ hx))
    refine ⟨w,hw,ih _ _ _ (Fin.cons w v) ?_ ?_⟩
    · intro x hx
      rw [hv,he] at hx; exact ht x (mem_union_right _ hx)
    · simpa only [updates,hv,he] using hu

end

open Classical Hereditary Counting HFCoding Finset

variable {R F : Type} {arity : F → ℕ}

def width : {k : ℕ} → Rule R F arity k → ℕ
  | _,.skip => 6
  | _,.update _ args value => 6+value.width+∑ j, (args j).width
  | _,.parallel r t => 6+width r+width t
  | _,.conditional c r t => 6+c.width+width r+width t
  | _,.forall b r | _,.letValue b r => 6+b.width+width r

variable {ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_graph (K : ℕ) {k n : ℕ} (r : Rule R F arity k) (f : F)
    (z : Fin n) (a : Fin (arity f) → Fin n) (v : Fin k → Fin n) (hm : n+r.width ≤ m) :
    UniformDefinable S m n (fun i w => Graph (d i) K (rel i) (s i) r f (w z) (w ∘ a) (w ∘ v)) := by
  have term {k n : ℕ} (t : Term R F arity k) (z : Fin n) (v : Fin k → Fin n) (ht : t.width ≤ m) :
      UniformDefinable S m n (fun i w => Term.Graph (d i) K (rel i) (s i) t (w z) (w ∘ v)) := by
    apply (Term.uniform_graph d S hd hp ha hmem hset rel s hinput hstate K t ht |>.reindex (Fin.cons z v)).congr
    intro i w
    simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons]
  induction r generalizing n with
  | skip => exact UniformDefinable.falsum
  | update g args value =>
    simp only [width] at hm
    by_cases h : g = f
    · subst g
      have hv := term value z v (by omega)
      have hag (j) := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (arity f)))) => Nat.zero_le (Term.width (args j))) (mem_univ j)
      have has := UniformDefinable.forall_finite (fun j => term (args j) (a j) v (by have := hag j; omega))
      apply (hv.and has).congr
      intro i w
      simp [Graph]
    · apply UniformDefinable.falsum.congr
      intro i w; simp only [Graph,dite_eq_right h]
  | parallel r t ir it =>
    simp only [width] at hm
    exact (ir z a v (by omega)).or (it z a v (by omega))
  | @conditional k c r t ir it =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+1) := Fin.succ ∘ v
    have hc := term c (0 : Fin (n+1)) vv (by omega)
    have hr := ir z.succ (Fin.succ ∘ a) vv (by omega)
    have ht := it z.succ (Fin.succ ∘ a) vv (by omega)
    have hb := (HFCoding.uniform_ordinal S hmem hset (by omega) hd hp 1).reindex (![0] : Fin 1 → Fin (n+1))
    apply ((hc.and ((hb.and hr).or (hb.neg.and ht))).ex (by omega)).congr
    intro i w
    simp only [Graph,vv,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    rfl
  | @«forall» k b r ih =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+2) := fun j => (v j).succ.succ
    have hb := term b (1 : Fin (n+2)) vv (by omega)
    have hx := hmem.reindex (![0,1] : Fin 2 → Fin (n+2))
    have hr := ih z.succ.succ (fun j => (a j).succ.succ) (Fin.cons 0 vv) (by omega)
    apply (((hb.and (hx.and hr)).ex (by omega)).ex (by omega)).congr
    intro i w
    change (∃ b' x, _ ∧ _ ∧ _) ↔ _
    simp only [Graph,vv,Fin.comp_cons,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    rfl
  | @letValue k b r ih =>
    simp only [width] at hm
    let vv : Fin k → Fin (n+1) := Fin.succ ∘ v
    have hb := term b (0 : Fin (n+1)) vv (by omega)
    have hr := ih z.succ (Fin.succ ∘ a) (Fin.cons 0 vv) (by omega)
    apply ((hb.and hr).ex (by omega)).congr
    intro i w
    simp only [Graph,vv,Fin.comp_cons,Fin.cons_zero,Fin.cons_succ]
    rfl

end CPTSeparation.Operational.Rule

end

end OAI
