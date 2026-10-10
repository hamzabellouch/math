import OAI.ModelTheory.Choiceless.Simulation

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type}

local instance : DecidableEq (HF A) := Classical.decEq _

def descendants (t : Finset (HF A)) : ℕ → Finset (HF A)
  | 0 => t
  | k+1 => descendants t k ∪ (descendants t k).biUnion elements

lemma descendants_mono (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ descendants t (k+1) := subset_union_left

lemma roots_subset_descendants (t : Finset (HF A)) (k : ℕ) : t ⊆ descendants t k := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih => exact ih.trans (descendants_mono t k)

lemma descendants_subset (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ familyClosure t := by
  induction k with
  | zero => exact fun _ hx => familyClosure_contains hx
  | succ k ih =>
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact ih hx
    · obtain ⟨y,hy,hxy⟩ := mem_biUnion.mp hx
      exact familyClosure_transitive (ih hy) hxy

lemma descendants_stable (t : Finset (HF A)) (k : ℕ)
    (hs : descendants t (k+1) ⊆ descendants t k) : descendants t k = familyClosure t := by
  apply subset_antisymm (descendants_subset t k)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
  have h := (mem_closure_iff x y).mp hxy
  have hc : ∀ {a b : HF A}, a ∈ b → b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hab hb
    exact hs (mem_union_right _ (mem_biUnion.mpr ⟨b,hb,hab⟩))
  have aux : ∀ {a b : HF A}, Relation.ReflTransGen (fun x y : HF A => x ∈ y) a b →
      b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hr
    induction hr with
    | refl => exact fun ha => ha
    | tail hab hbc ih => exact fun hb => ih (hc hbc hb)
  exact aux h (roots_subset_descendants t k hy)

lemma descendants_card_lower (t : Finset (HF A)) (k : ℕ)
    (hne : descendants t k ≠ familyClosure t) : k ≤ (descendants t k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hproper : descendants t k ⊂ descendants t (k+1) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨descendants_mono t k,?_⟩
      intro he
      exact hne (he.symm.trans (descendants_stable t k (he ▸ subset_rfl)))
    have hprev : descendants t k ≠ familyClosure t := by
      intro he
      exact hne (subset_antisymm (descendants_subset t (k+1)) (he ▸ descendants_mono t k))
    have hh := card_lt_card hproper
    have hi := ih hprev
    omega

lemma descendants_eq (t : Finset (HF A)) (K : ℕ) (hb : (familyClosure t).card ≤ K) :
    descendants t K = familyClosure t := by
  by_contra h
  have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨descendants_subset t K,h⟩)
  have hlow := descendants_card_lower t K h
  omega

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational.State

open Classical Hereditary Counting HFCoding Finset

variable {ι L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [finiteF : Fintype F] {arity : F → ℕ}

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (s : ∀ i, State F arity (A i))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

omit ι F A arity s in
lemma mem_critical_iff
    {ι : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (s : (i : ι) → Operational.State F arity (A i)) (i : ι) (x : HF (A i)) : x ∈ (s i).critical ↔
    ∃ f u, (s i).value ⟨f,u⟩ ≠ empty ∧ (x = (s i).value ⟨f,u⟩ ∨ ∃ j, x = u j) := by
  simp only [critical,mem_biUnion,mem_support,mem_insert,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨f,u⟩,h,he | ⟨j,he⟩⟩
    · exact ⟨f,u,h,Or.inl he⟩
    · exact ⟨f,u,h,Or.inr ⟨j,he.symm⟩⟩
  · rintro ⟨f,u,h,he | ⟨j,he⟩⟩
    · exact ⟨⟨f,u⟩,h,Or.inl he⟩
    · exact ⟨⟨f,u⟩,h,Or.inr ⟨j,he.symm⟩⟩

omit ι L F A arity d S m hd hp hmem hset s hstate in
lemma uniform_critical
    {ι : Type}
    {L : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (s : (i : ι) → Operational.State F arity (A i))
    (hstate : ∀ (f : F),
  Counting.UniformDefinable S m (arity f + 1) fun i v => ↑(v 0) = (s i).value ⟨f, fun j => ↑(v j.succ)⟩) (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).critical → x ∈ d i) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ (s i).critical) := by
  have hf (f : F) : UniformDefinable S m 1 (fun i v =>
      ∃ u : Fin (arity f) → Domain (d i), ∃ z : Domain (d i),
        z.val = (s i).value ⟨f,fun j => (u j).val⟩ ∧ z.val ≠ empty ∧
          ((v 0).val = z.val ∨ ∃ j, (v 0).val = (u j).val)) := by
    let a := arity f
    let ix : Fin 1 → Fin ((a+1)+1) := fun _ => Fin.natAdd (a+1) 0
    let iz : Fin ((arity f)+1) → Fin ((a+1)+1) := Fin.castAdd 1
    have hz := (hstate f).reindex iz
    have he := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (fun _ : Fin 1 => iz 0)
    have hv := (UniformDefinable.equal (S := S) (m := m) (ix 0) (iz 0))
    have hu := UniformDefinable.exists_finset univ (fun j (_ : j ∈ (univ : Finset (Fin a))) =>
      UniformDefinable.equal (S := S) (m := m) (ix 0) (iz j.succ))
    have hh := (hz.and (he.neg.and (hv.or hu))).exists_vec (by have := har f; change (arity f+1)+1 ≤ m; omega)
    apply hh.congr
    intro i v
    simp only [Finset.mem_univ,true_and] at hh
    constructor
    · rintro ⟨w,hw,hne,hout⟩
      refine ⟨fun j => w j.succ,w 0,?_,?_,?_⟩
      · simpa only [iz,Fin.append_left,Function.comp_apply] using hw
      · simpa only [iz,Fin.append_left,Function.comp_apply] using hne
      · rcases hout with he | ⟨j,_,he⟩
        · exact Or.inl (congrArg Subtype.val (by simpa [ix,iz,Fin.append_left,Fin.append_right] using he))
        · exact Or.inr ⟨j,congrArg Subtype.val (by simpa [ix,iz,Fin.append_left,Fin.append_right] using he)⟩
    · rintro ⟨u,z,hz,hne,hout⟩
      refine ⟨Fin.cons z u,?_,?_,?_⟩
      · simpa only [iz,Fin.append_left,Function.comp_apply,Fin.cons_zero,Fin.cons_succ] using hz
      · simpa only [iz,Fin.append_left,Function.comp_apply,Fin.cons_zero] using hne
      · rcases hout with he | ⟨j,he⟩
        · left; apply Subtype.ext; simpa [ix,iz,Fin.append_left,Fin.append_right] using he
        · right; refine ⟨j,mem_univ _,?_⟩; apply Subtype.ext; simpa [ix,iz,Fin.append_left,Fin.append_right] using he
  apply (UniformDefinable.exists_finset univ (fun f _ => hf f)).congr
  intro i v
  simp only [mem_univ,true_and]
  rw [mem_critical_iff s]
  constructor
  · rintro ⟨f,u,z,hz,hne,hout⟩
    exact ⟨f,fun j => (u j).val,hz ▸ hne,by simpa only [hz] using hout⟩
  · rintro ⟨f,u,hne,hout⟩
    let uu : Fin (arity f) → Domain (d i) := fun j => ⟨u j,hs i _ ((s i).argument_mem_critical hne j)⟩
    refine ⟨f,uu,⟨(s i).value ⟨f,u⟩,hs i _ ((s i).value_mem_critical hne)⟩,rfl,hne,?_⟩
    exact hout

def rootFamily {i : ι} (s : State F arity (A i)) : Finset (HF (A i)) :=
  s.critical ∪ {allAtoms,empty,truth} ∪ univ.image atom

include hd hp ha hmem hset hstate in
lemma uniform_roots (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ rootFamily (s i)) := by
  have hc := uniform_critical d S hd hp hmem hset s hstate hm har (fun i x hx =>
    hs i x (familyClosure_contains (mem_union_left _ (mem_union_left _ hx))))
  have hat := Operational.uniform_atoms d S hd ha hmem hset hm
  have he := HFCoding.uniform_ordinal S hmem hset hm hd hp 0
  have ht := HFCoding.uniform_ordinal S hmem hset hm hd hp 1
  apply (((hc.or (hat.or (he.or ht))).or hset.neg)).congr
  intro i v
  simp only [rootFamily,mem_union,mem_insert,Finset.mem_singleton,mem_image,mem_univ,true_and]
  have hh : (¬isSet (v 0).val = true) ↔ ∃ a, atom a = (v 0).val := by
    rcases atom_or_set (v 0).val with ⟨a,he⟩ | he
    · rw [he]; simp only [isSet_atom,Bool.false_eq_true,not_false_eq_true,true_iff]; exact ⟨a,rfl⟩
    · rw [he,isSet_ofFinset]; simp only [not_true_eq_false,false_iff,not_exists]
      intro a ha
      have h := congrArg isSet ha
      simp only [isSet_atom,isSet_ofFinset] at h
      cases h
  exact or_congr Iff.rfl hh

omit ι L A d S m hmem in
lemma uniform_descendants
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (t : ∀ i, Finset (HF (A i)))
    (ht : UniformDefinable S m 1 (fun i v => (v 0).val ∈ t i))
    (hs : ∀ i x, x ∈ familyClosure (t i) → x ∈ d i) (hm : 2 ≤ m) (k : ℕ) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ descendants (t i) k) := by
  induction k with
  | zero => exact ht
  | succ k ih =>
    have hh := ((ih.reindex (![0] : Fin 1 → Fin 2)).and
      (hmem.reindex (![1,0] : Fin 2 → Fin 2))).ex (by omega)
    apply (ih.or hh).congr
    intro i v
    change ((v 0).val ∈ descendants (t i) k ∨
      ∃ y : Domain (d i), y.val ∈ descendants (t i) k ∧ (v 0).val ∈ y.val) ↔ _
    simp only [descendants,mem_union,mem_biUnion]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨y,hy,hxy⟩; exact ⟨y.val,hy,hxy⟩
    · rintro ⟨y,hy,hxy⟩; exact ⟨⟨y,hs i y (descendants_subset _ _ hy)⟩,hy,hxy⟩

include hd hp ha hmem hset hstate in
lemma uniform_active (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) (K : ℕ)
    (hK : ∀ i, (s i).active.card ≤ K) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ (s i).active) := by
  have hroots := uniform_roots d S hd hp ha hmem hset s hstate hm har hs
  have hh := uniform_descendants d S hmem (fun i => rootFamily (s i)) hroots hs (by omega) K
  apply hh.congr
  intro i v
  have hi : (familyClosure (rootFamily (s i))).card ≤ K := hK i
  rw [descendants_eq (rootFamily (s i)) K hi]
  rfl

include hd hp ha hmem hset hstate in
lemma uniform_active_card (hm : 6 ≤ m) (har : ∀ f, arity f+2 ≤ m)
    (hs : ∀ i x, x ∈ (s i).active → x ∈ d i) (K : ℕ)
    (hK : ∀ i, (s i).active.card ≤ K) (k : ℕ) :
    UniformDefinable S m 0 (fun i _ => (s i).active.card = k) := by
  have hh := (uniform_active d S hd hp ha hmem hset s hstate hm har hs K hK).exact (by omega) k
  apply hh.congr
  intro i v
  change Nonempty ({x : Domain (d i) // x.val ∈ (s i).active} ≃ Fin k) ↔ _
  let e : {x : Domain (d i) // x.val ∈ (s i).active} ≃ {x // x ∈ (s i).active} :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,hs i x.val x.property⟩,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using h)))⟩

end CPTSeparation.Operational.State

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {ι R L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [Fintype F] {arity : F → ℕ}

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

omit ι L F A arity d S m in
lemma uniform_consistency
    {ι : Type}
    {L : Type}
    {F : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    [Fintype F]
    {arity : F → ℕ}
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ} (u : ∀ i, Finset (Update F arity (A i)))
    (hu : ∀ f, UniformDefinable S m (arity f+1) (fun i v =>
      (⟨f,fun j => (v j.succ).val⟩,(v 0).val) ∈ u i))
    (hd : ∀ i l z, (l,z) ∈ u i → z ∈ d i ∧ ∀ j, l.2 j ∈ d i)
    (hm : ∀ f, arity f+2 ≤ m) :
    UniformDefinable S m 0 (fun i _ => State.Consistent (u i)) := by
  have hf (f : F) : UniformDefinable S m 0 (fun i _ =>
      ∃ w : Fin (arity f+2) → Domain (d i),
        (⟨f,fun j => (w j.succ.succ).val⟩,(w 0).val) ∈ u i ∧
        (⟨f,fun j => (w j.succ.succ).val⟩,(w 1).val) ∈ u i ∧ (w 0).val ≠ (w 1).val) := by
    have h0 := (hu f).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (arity f+1) → Fin (arity f+2))
    have h1 := (hu f).reindex (Fin.cons 1 (fun j => j.succ.succ) : Fin (arity f+1) → Fin (arity f+2))
    have he := (UniformDefinable.equal (S := S) (m := m) (0 : Fin (arity f+2)) 1).neg
    have hh := (h0.and (h1.and he)).exists_vec (n := 0) (hm f)
    apply hh.congr
    intro i v
    apply exists_congr
    intro w
    have happ : Fin.append w v = w := Fin.append_right_nil w v rfl
    simp only [happ,Function.comp_apply,Fin.cons_zero,Fin.cons_succ]
    exact and_congr Iff.rfl (and_congr Iff.rfl (not_congr Subtype.val_injective.eq_iff.symm))
  apply (UniformDefinable.exists_finset univ (fun f _ => hf f)).neg.congr
  intro i v
  simp only [mem_univ,true_and]
  constructor
  · intro h l x y hx hy
    by_contra hne
    let w : Fin (arity l.1+2) → Domain (d i) := Fin.cons ⟨x,(hd i l x hx).1⟩
      (Fin.cons ⟨y,(hd i l y hy).1⟩ (fun j => ⟨l.2 j,(hd i l x hx).2 j⟩))
    exact h ⟨l.1,w,hx,hy,hne⟩
  · intro hc
    rintro ⟨f,w,hx,hy,hne⟩
    exact hne (hc _ _ _ hx hy)

end CPTSeparation.Operational

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_observations_agree (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (∀ c, P.flag (ss false h) c ↔ P.flag (ss true h) c) ∧
    (State.Consistent (P.rule.updates (atomInput (twoCharges vstar false)).rel (ss false h) Fin.elim0) ↔
      State.Consistent (P.rule.updates (atomInput (twoCharges vstar true)).rel (ss true h) Fin.elim0)) ∧
    (ss false h).active.card = (ss true h).active.card := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ P.runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) P hn h K N hN (hbound i) q hq hb
  have ht : ∀ i j, j ≤ h → ∀ x ∈ P.rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := P.rule_trace_subset (atomInput (twoCharges vstar i)).rel hj (hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ P.runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact P.runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans (P.card_runTrace_le _ h K (hbound i))
  let := P.finiteFunctions
  have htrans : ∀ Q : Bool → Prop, UniformDefinable C m 0 (fun i _ => Q i) → (Q false ↔ Q true) := by
    intro Q hQ
    obtain ⟨φ,hφ,hφsem⟩ := hQ (Fin.elim0 : Fin 0 → Fin m)
    have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
    let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
    let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
    let := atom_nonempty hn (0 : Vertex n → Scalar)
    let := atom_nonempty hn (Pi.single vstar 1)
    exact (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
      hwidth hhom hgiant φ hfree v w).trans (hφsem true w))
  have hstate := P.uniform_run D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h ((h+1)*(K+P.rule.bound.eval K)) hr hm hroom (fun i j hj => ht i j (by omega))
  have hac : ∀ i x, x ∈ (ss i h).active → x ∈ D i := by
    intro i x hx
    exact hfamily i x (P.active_subset_trace _ (le_refl h) (hr i h (le_refl h)) hx)
  have har : ∀ f, P.functionArity f+2 ≤ m := fun f => by have := hm f; omega
  refine ⟨?_,?_,?_⟩
  · intro c
    apply htrans (fun i => P.flag (ss i h) c)
    exact P.uniform_flag D C (program_domain_transitive (twoCharges vstar))
      (program_pure (twoCharges vstar) hn) (program_mem_uniform (twoCharges vstar))
      (program_set_uniform (twoCharges vstar)) (fun i => ss i h) hstate hroom c
  · apply htrans (fun i => State.Consistent (P.rule.updates (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0))
    apply uniform_consistency D C
      (fun i => P.rule.updates (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0)
    · intro f
      exact uniform_updates D C (program_domain_transitive (twoCharges vstar))
        (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
        (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
        (fun i => (atomInput (twoCharges vstar i)).rel) (fun i => ss i h)
        (op_input_uniform (twoCharges vstar)) hstate ((h+1)*(K+P.rule.bound.eval K)) P.rule f
        (by have := hm f; omega) (fun i x hx => ht i h (le_refl h) x hx)
    · intro i l z hz
      have hh := P.rule.closure_update_subset_trace (atomInput (twoCharges vstar i)).rel (ss i h) Fin.elim0 hz
      exact ⟨(ht i h (le_refl h) z (hh.1 (mem_closure_self z))).1,
        fun j => (ht i h (le_refl h) (l.2 j) (hh.2 j (mem_closure_self _))).1⟩
    · exact har
  · have hc := State.uniform_active_card D C (program_domain_transitive (twoCharges vstar))
      (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
      (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
      (fun i => ss i h) hstate hroom har hac K (fun i => ha i h (le_refl h)) (ss false h).active.card
    exact ((htrans _ hc).mp rfl).symm

end CPTSeparation.Grid

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} [Fintype A] {arity : F → ℕ}

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

namespace State

lemma active_apply_subset (rel : R → A → A → Bool) (s : State F arity A)
    (r : Rule R F arity 0) :
    (s.applyUpdates (r.updates rel s Fin.elim0)).active ⊆ s.active ∪ r.trace rel s Fin.elim0 := by
  let u := r.updates rel s Fin.elim0
  have hc : Closed (s.active ∪ r.trace rel s Fin.elim0) :=
    Closed.union (fun x hx y hy => s.active_transitive hx hy) (r.trace_closed rel s Fin.elim0)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
  apply closure_subset_of_transitive hc (x := y) ?_ hxy
  rcases mem_union.mp hy with hy | hy
  · rcases mem_union.mp hy with hy | hy
    · obtain ⟨l,hl,hy⟩ := mem_biUnion.mp hy
      have hn := (mem_support (s.applyUpdates u) l).mp hl
      by_cases hu : ∃ z, (l,z) ∈ u
      · have hv : (l,(s.applyUpdates u).value l) ∈ u := by
          change (l,s.updatedValue u l) ∈ u
          simp only [updatedValue,dite_eq_left hu]
          exact hu.choose_spec
        have ht := r.closure_update_subset_trace rel s Fin.elim0 hv
        rcases mem_insert.mp hy with he | hy
        · subst y; exact mem_union_right _ (ht.1 (mem_closure_self _))
        · obtain ⟨j,hj,he⟩ := mem_image.mp hy
          subst y
          exact mem_union_right _ (ht.2 j (mem_closure_self _))
      · have he : (s.applyUpdates u).value l = s.value l := s.updatedValue_default u hu
        have hn' : s.value l ≠ empty := he ▸ hn
        rcases mem_insert.mp hy with hy | hy
        · rw [hy,he]
          exact mem_union_left _ (s.closure_value_subset_active l (mem_closure_self _))
        · obtain ⟨j,hj,heq⟩ := mem_image.mp hy
          subst y
          exact mem_union_left _ (familyClosure_contains (mem_union_left _ (mem_union_left _ (s.argument_mem_critical hn' j))))
    · exact mem_union_left _ (familyClosure_contains (mem_union_left _ (mem_union_right _ hy)))
  · exact mem_union_left _ (familyClosure_contains (mem_union_right _ hy))

lemma initial_active_card : (initial : State F arity A).active.card ≤ Fintype.card A+3 := by
  let t : Finset (HF A) := {allAtoms,empty,truth} ∪ univ.image atom
  have hc : Closed t := by
    intro x hx y hy
    rcases mem_union.mp hx with hx | hx
    · simp only [mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_union_right _ (by simpa only [allAtoms,mem_ofFinset] using hy)
      · obtain ⟨k,hk,he⟩ := (mem_ordinal y 0).mp hy
        omega
      · obtain ⟨k,hk,he⟩ := (mem_ordinal y 1).mp hy
        have hk0 : k = 0 := by omega
        rw [he,hk0]
        exact mem_union_left _ (by simp)
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      have hh : y ∈ (∅ : Finset (HF A)) := hy
      exact (notMem_empty _ hh).elim
  have he : (initial : State F arity A).critical = ∅ := by
    ext x
    simp [critical,mem_support,initial]
  have hsub : (initial : State F arity A).active ⊆ t := by
    intro x hx
    change x ∈ familyClosure _ at hx
    rw [he,empty_union] at hx
    obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
    exact closure_subset_of_transitive hc hy hxy
  apply (card_le_card hsub).trans
  have h3 : ({allAtoms,empty,truth} : Finset (HF A)).card ≤ 3 := by
    have h1 := card_insert_le (allAtoms : HF A) ({empty,truth} : Finset (HF A))
    have h2 := card_insert_le (empty : HF A) ({truth} : Finset (HF A))
    simp only [card_singleton] at h2
    omega
  have hi : (univ.image (atom : A → HF A)).card ≤ Fintype.card A := card_image_le.trans (by simp)
  exact (card_union_le _ _).trans (by omega)

end State

namespace Machine

variable (P : Machine R)

def boundedAccepts (rel : R → A → A → Bool) (time space : ℕ) : Prop :=
  ∃ h st, h ≤ time ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    ∀ j, j ≤ h → ∀ t, P.run rel j = some t → t.active.card ≤ space

lemma step_exists_iff (rel : R → A → A → Bool) (s : P.Store (A := A)) :
    (∃ t, P.step rel s = some t) ↔ P.flag s .halt ∨ State.Consistent (P.rule.updates rel s Fin.elim0) := by
  unfold step
  split
  · simp_all
  · dsimp only
    split <;> simp_all

lemma active_step_bound (rel : R → A → A → Bool) {s t : P.Store (A := A)}
    (he : P.step rel s = some t) (K : ℕ) (hK : s.active.card ≤ K) :
    t.active.card ≤ K+P.rule.bound.eval K := by
  unfold step at he
  split at he
  · have ht := Option.some.inj he
    subst t
    exact hK.trans (Nat.le_add_right _ _)
  · dsimp only at he
    split at he
    · have ht := Option.some.inj he
      subst t
      apply (card_le_card (State.active_apply_subset rel s P.rule)).trans
      apply (card_union_le _ _).trans
      apply add_le_add hK
      apply P.rule.card_trace_le rel s Fin.elim0 K
      simpa only [Term.potential,univ_eq_empty,Finset.sum_empty,Nat.add_zero] using hK
    · contradiction

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R : Type} {A : Bool → Type} [∀ i, Fintype (A i)]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R) (rel : ∀ i, R → A i → A i → Bool)

def PrefixBound (h K : ℕ) : Prop :=
  ∀ i j, j ≤ h → ∃ st, P.run (rel i) j = some st ∧ st.active.card ≤ K

def ObservationsAt (h : ℕ) : Prop :=
  ∀ (i j : Bool) (s : P.Store (A := A i)) (t : P.Store (A := A j)),
    P.run (rel i) h = some s → P.run (rel j) h = some t →
      (∀ c, P.flag s c ↔ P.flag t c) ∧
      (State.Consistent (P.rule.updates (rel i) s Fin.elim0) ↔
        State.Consistent (P.rule.updates (rel j) t Fin.elim0)) ∧ s.active.card = t.active.card

lemma bounded_accept_transfer (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := A i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (i j : Bool) (hacc : P.boundedAccepts (rel i) time space) :
    P.boundedAccepts (rel j) time space := by
  by_cases hij : i = j
  · subst j; exact hacc
  have hcases (b : Bool) : b = i ∨ b = j := by cases i <;> cases j <;> cases b <;> simp_all
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := hacc
  have hsource (k : ℕ) (hk : k ≤ h) : ∃ u, P.run (rel i) k = some u ∧ u.active.card ≤ space := by
    obtain ⟨u,hu⟩ := P.run_prefix_exists (rel i) hhr hk
    exact ⟨u,hu,hbudget k hk u hu⟩
  have hext : ∀ k, k ≤ h → ∃ t, P.run (rel j) k = some t ∧
      ∀ l, l ≤ k → ∀ u, P.run (rel j) l = some u → u.active.card ≤ space := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hp : P.PrefixBound rel 0 K := by
        intro b l hl
        have he : l = 0 := by omega
        subst l
        exact ⟨State.initial,rfl,hroot b⟩
      have ho := hobs 0 (by omega) hp i j State.initial State.initial rfl rfl
      have hb := hbudget 0 (by omega) State.initial rfl
      refine ⟨State.initial,rfl,?_⟩
      intro l hl u hu
      have he : l = 0 := by omega
      subst l
      have hh : State.initial = u := Option.some.inj hu
      subst u
      omega
    | succ k ih =>
      intro hkh
      obtain ⟨t,hrt,hbt⟩ := ih (by omega)
      obtain ⟨s,hrs,hbs⟩ := hsource k (by omega)
      obtain ⟨s1,hrs1,hbs1⟩ := hsource (k+1) hkh
      have hp : P.PrefixBound rel k K := by
        intro b l hl
        rcases hcases b with rfl | rfl
        · obtain ⟨u,hu,hbu⟩ := hsource l (by omega)
          exact ⟨u,hu,hbu.trans hS⟩
        · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt hl
          exact ⟨u,hu,(hbt l hl u hu).trans hS⟩
      have ho := hobs k (by omega) hp i j s t hrs hrt
      have hstep : P.step (rel i) s = some s1 := by
        simpa only [run,hrs,Option.bind_some] using hrs1
      have hsuc : ∃ t1, P.step (rel j) t = some t1 := by
        apply (P.step_exists_iff (rel j) t).mpr
        rcases (P.step_exists_iff (rel i) s).mp ⟨s1,hstep⟩ with hf | hc
        · exact Or.inl ((ho.1 .halt).mp hf)
        · exact Or.inr (ho.2.1.mp hc)
      obtain ⟨t1,ht1⟩ := hsuc
      have hrt1 : P.run (rel j) (k+1) = some t1 := by
        simp only [run,hrt,Option.bind_some,ht1]
      have hbt1 : t1.active.card ≤ K :=
        (P.active_step_bound (rel j) ht1 space (hbt k (le_refl k) t hrt)).trans hnext
      have hp1 : P.PrefixBound rel (k+1) K := by
        intro b l hl
        rcases hcases b with rfl | rfl
        · obtain ⟨u,hu,hbu⟩ := hsource l (by omega)
          exact ⟨u,hu,hbu.trans hS⟩
        · by_cases he : l = k+1
          · subst l; exact ⟨t1,hrt1,hbt1⟩
          · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt (j := l) (by omega)
            exact ⟨u,hu,(hbt l (by omega) u hu).trans hS⟩
      have ho1 := hobs (k+1) (by omega) hp1 i j s1 t1 hrs1 hrt1
      have ht1small : t1.active.card ≤ space := by rw [← ho1.2.2]; exact hbs1
      refine ⟨t1,hrt1,?_⟩
      intro l hl u hu
      by_cases he : l = k+1
      · subst l
        have hh : u = t1 := Option.some.inj (hu.symm.trans hrt1)
        exact hh ▸ ht1small
      · exact hbt l (by omega) u hu
  obtain ⟨t,hrt,hbt⟩ := hext h (le_refl h)
  have hp : P.PrefixBound rel h K := by
    intro b l hl
    rcases hcases b with rfl | rfl
    · obtain ⟨u,hu,hbu⟩ := hsource l hl
      exact ⟨u,hu,hbu.trans hS⟩
    · obtain ⟨u,hu⟩ := P.run_prefix_exists _ hrt hl
      exact ⟨u,hu,(hbt l hl u hu).trans hS⟩
  have ho := hobs h hht hp i j st t hhr hrt
  exact ⟨h,t,hht,hrt,(ho.1 .halt).mp hhf,(ho.1 .accept).mp hha,hbt⟩

lemma bounded_accept_iff (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := A i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h) :
    P.boundedAccepts (rel false) time space ↔ P.boundedAccepts (rel true) time space :=
  ⟨P.bounded_accept_transfer rel time space K hS hnext hroot hobs false true,
   P.bounded_accept_transfer rel time space K hS hnext hroot hobs true false⟩

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_prefix_observations (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (hr : P.PrefixBound (fun i => (atomInput (twoCharges vstar i)).rel) h K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    P.ObservationsAt (fun i => (atomInput (twoCharges vstar i)).rel) h := by
  let ss := fun i j => (P.run (atomInput (twoCharges vstar i)).rel j).getD State.initial
  have hrs : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j) := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simp only [ss,hst,Option.getD_some]
  have hact : ∀ i j, j ≤ h → (ss i j).active.card ≤ K := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simpa only [ss,hst,Option.getD_some] using hb
  have ho := op_observations_agree P vstar hn h K hN ss hrs hact q hq hb hm hroom hs hwidth hhom hgiant
  intro i j st tt hst htt
  have he : st = ss i h := Option.some.inj (hst.symm.trans (hrs i h (le_refl h)))
  have he' : tt = ss j h := Option.some.inj (htt.symm.trans (hrs j h (le_refl h)))
  subst st; subst tt
  cases i <;> cases j
  · exact ⟨fun _ => Iff.rfl,Iff.rfl,rfl⟩
  · exact ho
  · exact ⟨fun c => (ho.1 c).symm,ho.2.1.symm,ho.2.2.symm⟩
  · exact ⟨fun _ => Iff.rfl,Iff.rfl,rfl⟩

end CPTSeparation.Grid

namespace CPTSeparation.PolynomialCost

lemma eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

end CPTSeparation.PolynomialCost

namespace CPTSeparation.Operational.Machine

def cutoffAccepts {A : Type} [Fintype A] {R : Type} (P : Machine R) (c d : ℕ)
    (rel : R → A → A → Bool) : Prop :=
  P.boundedAccepts rel (c*(Fintype.card A+1)^d) (c*(Fintype.card A+1)^d)

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n : ℕ}

lemma atom_card_independent (hn : 1 ≤ n) (b b' : Vertex n → Scalar) :
    Fintype.card (Atom b) = Fintype.card (Atom b') := by
  have hv (v : Vertex n) : ∃ t : Edge n → Scalar, boundary t v = b' v - b v := by
    obtain ⟨e,he⟩ := exists_head_or_tail hn v
    rcases he with he | he
    · refine ⟨Pi.single e (b' v-b v),?_⟩
      rw [boundary_single]
      subst v
      simp [head_ne_tail]
    · refine ⟨Pi.single e (-(b' v-b v)),?_⟩
      rw [boundary_single]
      subst v
      simp [Ne.symm (head_ne_tail e)]
  choose tv htv using hv
  exact Fintype.card_congr (blockShiftEquiv (fun _ _ => 0) tv htv)

end CPTSeparation.Grid

namespace CPTSeparation.Operational.Machine

lemma boundedAccepts_fintype {A R : Type} (t u : Fintype A) (P : Machine R)
    (rel : R → A → A → Bool) (T S : ℕ) :
    @boundedAccepts A R t P rel T S ↔ @boundedAccepts A R u P rel T S := by
  have h : t = u := Subsingleton.elim _ _
  cases h
  rfl

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

theorem cutoff_agrees_on_some_box (P : Operational.Machine Symbol) (c d : ℕ) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (vstar : Vertex n),
      P.cutoffAccepts c d (atomInput (0 : Vertex n → Scalar)).rel ↔
        P.cutoffAccepts c d (atomInput (Pi.single vstar 1)).rel := by
  obtain ⟨m,hroom,hm⟩ := P.exists_palette
  let p₀ : Polynomial ℕ := Polynomial.X+P.rule.bound
  let p : Polynomial ℕ := (Polynomial.X+1)*(p₀+P.rule.bound.comp p₀)
  obtain ⟨cp,dp,hp⟩ := PolynomialCost.eval_bound p
  let e := timeExponent c d+2
  let a := timeExponent cp dp
  let q := e*a
  have he : 4 ≤ e := by have := timeExponent_ge_two c d; omega
  have ha : 2 ≤ a := timeExponent_ge_two cp dp
  have hq : 0 < q := Nat.mul_pos (by omega) (by omega)
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^e
  let K := B+P.rule.bound.eval B
  let vstar : Vertex n := ⟨0,0,0⟩
  let rel := fun i => (atomInput (twoCharges vstar i)).rel
  let space := c*(Fintype.card (Atom (0 : Vertex n → Scalar))+1)^d
  have hN : 2 ≤ N := hnum.1
  have hinput : ∀ i, Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hBB : N^timeExponent c d ≤ B := Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1.trans hBB
  have hinit : N+3 ≤ B := by
    have hs : 4 ≤ N^2 := by nlinarith
    have ht := Nat.mul_le_mul_left N hs
    calc
      N+3 ≤ N^3 := by nlinarith
      _ ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hspace : space ≤ B := by
    exact (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right (hinput false) 1) d)).trans
      ((polynomial_bounds c d N hN).2.2.1.trans hBB)
  have hsK : space ≤ K := hspace.trans (Nat.le_add_right _ _)
  have hnext : space+P.rule.bound.eval space ≤ K :=
    add_le_add hspace (PolynomialCost.eval_mono _ hspace)
  have hroot (i : Bool) : (State.initial : P.Store (A := Atom (twoCharges vstar i))).active.card ≤ K :=
    State.initial_active_card.trans ((Nat.add_le_add_right (hinput i) 3).trans (hinit.trans (Nat.le_add_right _ _)))
  have hpoly (h : ℕ) (hh : h ≤ space) : (h+1)*(K+P.rule.bound.eval K) ≤ N^q := by
    calc
      (h+1)*(K+P.rule.bound.eval K) ≤ (B+1)*(K+P.rule.bound.eval K) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = p.eval B := by simp only [p,p₀,K,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
      _ ≤ cp*(B+1)^dp := hp B
      _ ≤ B^a := (polynomial_bounds cp dp B hB).2.2.1
      _ = N^q := by simp only [B,q,pow_mul]
  have hh := P.bounded_accept_iff rel space space K hsK hnext hroot (fun h hht hprefix =>
    op_prefix_observations (N := N) P vstar hn h K (by omega) hprefix (q:ℝ) (by positivity)
      (by rw [Real.rpow_natCast]; exact_mod_cast hpoly h hht) hm hroom
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2)
  refine ⟨n,hn,vstar,?_⟩
  have hcard := atom_card_independent hn (0 : Vertex n → Scalar) (Pi.single vstar 1)
  simp only [Operational.Machine.cutoffAccepts,rel,space,twoCharges,← hcard] at hh ⊢
  convert hh using 1 <;> apply Operational.Machine.boundedAccepts_fintype

end CPTSeparation.Grid

end

end OAI
