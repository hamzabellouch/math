import OAI.Computability.WitnessedChoice.CumulativeEvaluation

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

local instance {A : Type*} : DecidableEq (HF A) := Classical.decEq _

lemma TC_eq_familyClosure {A : Type} (x : HF A) : TC x = familyClosure (elements x) := by
  ext y
  simp only [TC,familyClosure,Finset.mem_biUnion]

lemma descendants_TC_subset {A : Type} (x : HF A) (k : ℕ) :
    descendants (elements x) k ⊆ TC x := by
  rw [TC_eq_familyClosure]
  exact descendants_subset _ _

lemma descendants_TC_bound {A : Type} (x : HF A) (p : ℕ) :
    (TC x).card ≤ p ↔ (descendants (elements x) (p+1)).card ≤ p := by
  constructor
  · exact fun h => (Finset.card_le_card (descendants_TC_subset x _)).trans h
  · intro h
    by_cases he : descendants (elements x) (p+1) = TC x
    · rwa [he] at h
    · have he' : descendants (elements x) (p+1) ≠ familyClosure (elements x) := by
        simpa only [TC_eq_familyClosure] using he
      have hh := descendants_card_lower (elements x) (p+1) he'
      omega

lemma TC_closed {A : Type} (x : HF A) {y : HF A} (hy : y ∈ TC x)
    {z : HF A} (hz : z ∈ y) : z ∈ TC x := by
  rw [TC_eq_familyClosure] at hy ⊢
  exact familyClosure_transitive hy hz

lemma TC_in_domain {A : Type} (d : Set (HF A))
    (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {x : HF A} (hx : x ∈ d) :
    ∀ y ∈ TC x, y ∈ d := by
  intro y hy
  rw [TC_eq_familyClosure] at hy
  obtain ⟨z,hz,hyz⟩ := mem_familyClosure.mp hy
  have hz' : z ∈ d := hd x hx z hz
  have hr := (mem_closure_iff _ _).mp hyz
  clear hx hz hyz
  induction hr with
  | refl => exact hz'
  | @tail u v huv hvz ih => exact ih (hd _ hz' _ hvz)

variable {ι R : Type} {A : ι → Type}

variable (d : ∀ i, Set (HF (A i)))

variable (S : ∀ i, WitnessedSeparation.Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hm : 3 ≤ m)

include hd hmem hm

lemma uniform_descendants (k : ℕ) : UniformDefinable S m 2
    (fun _ v => (v 0).val ∈ descendants (elements (v 1).val) k) := by
  induction k with
  | zero => exact hmem
  | succ k ih =>
    have hleft := ih.reindex (![0,2] : Fin 2 → Fin 3)
    have hright := hmem.reindex (![1,0] : Fin 2 → Fin 3)
    apply (ih.or ((hleft.and hright).ex (by omega))).congr
    intro i v
    change ((v 0).val ∈ descendants (elements (v 1).val) k ∨
      ∃ z : Domain (d i), z.val ∈ descendants (elements (v 1).val) k ∧
        (v 0).val ∈ z.val) ↔ _
    simp only [descendants,Finset.mem_union,Finset.mem_biUnion]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨z,hz,hy⟩; exact ⟨z.val,hz,hy⟩
    · rintro ⟨z,hz,hy⟩
      exact ⟨⟨z,TC_in_domain (d i) (hd i) (v 1).property z
        (descendants_TC_subset _ _ hz)⟩,hz,hy⟩

omit hmem hm in
lemma descendants_count_iff (i : ι) (x : Domain (d i)) (k j : ℕ) :
    Nonempty ({y : Domain (d i) // y.val ∈ descendants (elements x.val) k} ≃ Fin j) ↔
      (descendants (elements x.val) k).card = j := by
  let t := descendants (elements x.val) k
  have ht : ∀ y ∈ t, y ∈ d i := fun y hy =>
    TC_in_domain (d i) (hd i) x.property y (descendants_TC_subset _ _ hy)
  let e : {y : Domain (d i) // y.val ∈ t} ≃ {y // y ∈ t} :=
    { toFun := fun y => ⟨y.val.val,y.property⟩
      invFun := fun y => ⟨⟨y.val,ht y.val y.property⟩,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have hh := Fintype.card_congr (e.symm.trans f)
    simpa [t] using hh
  · intro hh
    let f := (Fintype.equivFin {y // y ∈ t}).trans (finCongr (by simpa [t] using hh))
    exact ⟨e.trans f⟩

lemma uniform_TC_bound (p : ℕ) : UniformDefinable S m 1
    (fun _ v => (TC (v 0).val).card ≤ p) := by
  have hr := uniform_descendants d S hd hmem hm (p+1)
  have hh := UniformDefinable.exists_finset (Finset.range (p+1))
    (fun j _ => hr.exact (by omega : 1 < m) j)
  apply hh.congr
  intro i v
  simp only [Fin.cons_zero,Fin.cons_one,descendants_count_iff d hd,Finset.mem_range,Nat.lt_succ_iff]
  rw [descendants_TC_bound]
  exact ⟨fun ⟨j,hj,he⟩ => he ▸ hj,fun h => ⟨_,h,rfl⟩⟩

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

abbrev Traced (A : Type) (X : Type) := X × Finset (HF A)

def tracedLoop {A : Type} (p : ℕ) (step : HF A → Traced A (HF A)) :
    ℕ → HF A → Traced A (HF A)
  | 0, _ => (emptyHF, closure emptyHF)
  | fuel+1, x =>
      if (TC x).card ≤ p then
        let r := step x
        if x = r.1 then (x,r.2) else
          let s := tracedLoop p step fuel r.1
          (s.1,r.2 ∪ s.2)
      else (emptyHF,closure emptyHF)

mutual
  def Term.traced {A : Type} [Fintype A] (S : Input A) (p : ℕ) :
      {n : ℕ} → Term n → (Fin n → HF A) → Traced A (HF A)
    | _, .var j, env => (env j,closure (env j))
    | _, .empty, _ => (emptyHF,closure emptyHF)
    | _, .atoms, _ =>
        let x := ofFinset (Finset.univ.image atom)
        (x,closure x)
    | _, .pair a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (double x.1 y.1,insert (double x.1 y.1) (x.2 ∪ y.2))
    | _, .union a, env =>
        let x := a.traced S p env
        (unionHF x.1,insert (unionHF x.1) x.2)
    | _, .unique a, env =>
        let x := a.traced S p env
        (uniqueHF x.1,insert (uniqueHF x.1) x.2)
    | _, .card a, env =>
        let x := a.traced S p env
        (cardHF x.1,closure (cardHF x.1) ∪ x.2)
    | _, .comprehend body range guard, env =>
        let r := range.traced S p env
        let test := fun x => guard.traced S p (Fin.cons x env)
        let val := fun x => body.traced S p (Fin.cons x env)
        let selected := (elements r.1).filter (fun x => (test x).1 = true)
        let out := ofFinset (selected.image (fun x => (val x).1))
        (out, insert out (r.2 ∪ (elements r.1).biUnion (fun x => (test x).2) ∪
          selected.biUnion (fun x => (val x).2)))
    | _, .iterate step, env =>
        tracedLoop p (fun x => step.traced S p (Fin.cons x env)) (p+1) emptyHF
  def Formula.traced {A : Type} [Fintype A] (S : Input A) (p : ℕ) :
      {n : ℕ} → Formula n → (Fin n → HF A) → Traced A Bool
    | _, .equal a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (decide (x.1 = y.1),x.2 ∪ y.2)
    | _, .input r a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (inputHF S r x.1 y.1,x.2 ∪ y.2)
    | _, .neg a, env =>
        let x := a.traced S p env
        (!x.1,x.2)
    | _, .and a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (x.1 && y.1,x.2 ∪ y.2)
    | _, .or a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (x.1 || y.1,x.2 ∪ y.2)
    | _, .wsc _ _ _ _, _ => (false,∅)
end

variable {A : Type} [Fintype A]

omit [Fintype A] in
lemma iterationLoop_traced (q : ℕ) (step : HF A → Result (HF A))
    (ts : HF A → Traced A (HF A)) (h : ∀ x, step x = some (ts x).1)
    (fuel : ℕ) (x : HF A) :
    iterationLoop q step fuel x = some (tracedLoop q ts fuel x).1 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    by_cases hx : (TC x).card ≤ q
    · simp only [iterationLoop,tracedLoop,ite_eq_left hx,h x,Option.bind_some]
      by_cases he : x = (ts x).1
      · simp only [ite_eq_left he]
      · simp only [ite_eq_right he]
        exact ih _
    · simp only [iterationLoop,tracedLoop,ite_eq_right hx]

mutual
  theorem Term.eval_traced (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (t : Term n) (ht : t.wscCount = 0) (env : Fin n → HF A) :
      t.eval S p env = some (t.traced S (resource p (Fintype.card A)) env).1 := by
    cases t with
    | var j => rfl
    | empty => rfl
    | atoms =>
      simp only [Term.eval,Term.traced]
    | pair a b =>
      have h := Nat.add_eq_zero_iff.mp ht
      simp only [Term.eval,Term.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | union a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | unique a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | card a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | comprehend body range guard =>
      have h := Nat.add_eq_zero_iff.mp ht
      have h' := Nat.add_eq_zero_iff.mp h.1
      simp only [Term.eval,range.eval_traced S p h'.2 env,Option.bind_some]
      have hg : ∀ x : HF A, guard.eval S p (Fin.cons x env) =
          some (guard.traced S (resource p (Fintype.card A)) (Fin.cons x env)).1 :=
        fun x => guard.eval_traced S p h.2 _
      have hb : ∀ x : HF A, body.eval S p (Fin.cons x env) =
          some (body.traced S (resource p (Fintype.card A)) (Fin.cons x env)).1 :=
        fun x => body.eval_traced S p h'.1 _
      simp only [collect,hg,hb,Option.isSome_some,
        implies_true,and_self,ite_true,Option.getD_some,Term.traced,Option.some.injEq]
    | iterate step =>
      exact iterationLoop_traced _ _ _
        (fun x => step.eval_traced S p ht (Fin.cons x env)) _ _
  theorem Formula.eval_traced (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (f : Formula n) (hf : f.wscCount = 0) (env : Fin n → HF A) :
      f.eval S p env = some (f.traced S (resource p (Fintype.card A)) env).1 := by
    cases f with
    | equal a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | input r a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | neg a => simp only [Formula.eval,Formula.traced,a.eval_traced S p hf env,Option.map_some]
    | and a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | or a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | wsc step choice witness output => simp only [Formula.wscCount] at hf; omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

def ClosedTrace (F : Finset (HF A)) : Prop := ∀ x ∈ F, closure x ⊆ F

lemma closedTrace_closure (x : HF A) : ClosedTrace (closure x) := by
  intro y hy
  exact closure_subset_of_transitive (fun z hz w hw => closure_transitive hz hw) hy

lemma closedTrace_union {F G : Finset (HF A)} (hF : ClosedTrace F) (hG : ClosedTrace G) :
    ClosedTrace (F ∪ G) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (hF _ hx hy)
  · exact Finset.mem_union_right _ (hG _ hx hy)

lemma closedTrace_biUnion {X : Type} (t : Finset X) (f : X → Finset (HF A))
    (hf : ∀ x ∈ t, ClosedTrace (f x)) : ClosedTrace (t.biUnion f) := by
  intro x hx y hy
  obtain ⟨z,hz,hxz⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨z,hz,hf z hz _ hxz hy⟩

lemma closedTrace_insert {F : Finset (HF A)} (hF : ClosedTrace F) (x : HF A)
    (hx : closure x ⊆ insert x F) : ClosedTrace (insert x F) := by
  intro y hy z hz
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hx hz
  · exact Finset.mem_insert_of_mem (hF y hy hz)

lemma closure_emptyHF : closure (emptyHF : HF A) = {emptyHF} := by
  simp only [emptyHF,closure_ofFinset,familyClosure,Finset.biUnion_empty,Finset.insert_empty]

lemma closure_unionHF_subset (x : HF A) :
    closure (unionHF x) ⊆ insert (unionHF x) (closure x) := by
  rw [unionHF,closure_ofFinset]
  intro z hz
  simp only [Finset.mem_insert] at hz
  rcases hz with he | hz
  · exact Finset.mem_insert.mpr (Or.inl he)
  apply Finset.mem_insert_of_mem
  obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
  obtain ⟨w,hw,hyw⟩ := Finset.mem_biUnion.mp hy
  exact (closure_member_subset hw) ((closure_member_subset hyw) hzy)

lemma closure_uniqueHF_subset (x : HF A) :
    closure (uniqueHF x) ⊆ insert (uniqueHF x) (closure x) := by
  unfold uniqueHF
  split
  · rename_i h
    have hm : h.choose ∈ x := by
      change h.choose ∈ elements x
      exact Eq.mpr (congrArg (fun t : Finset (HF A) => h.choose ∈ t) h.choose_spec)
        (Finset.mem_singleton_self _)
    exact (closure_member_subset hm).trans (Finset.subset_insert _ _)
  · rw [closure_emptyHF]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

lemma tracedLoop_closure_subset (p : ℕ) (step : HF A → Traced A (HF A))
    (hs : ∀ x, closure (step x).1 ⊆ (step x).2) (fuel : ℕ) (x : HF A) :
    closure (tracedLoop p step fuel x).1 ⊆ (tracedLoop p step fuel x).2 := by
  induction fuel generalizing x with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs with hb he
    · calc
        closure x = closure (step x).1 := congrArg closure he
        _ ⊆ (step x).2 := hs x
    · exact (ih _).trans Finset.subset_union_right
    · exact Finset.Subset.refl _

lemma tracedLoop_closed (p : ℕ) (step : HF A → Traced A (HF A))
    (hs : ∀ x, ClosedTrace (step x).2) (fuel : ℕ) (x : HF A) :
    ClosedTrace (tracedLoop p step fuel x).2 := by
  induction fuel generalizing x with
  | zero => exact closedTrace_closure _
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs
    · exact hs x
    · exact closedTrace_union (hs x) (ih _)
    · exact closedTrace_closure _

variable [Fintype A]

lemma Term.traced_closure (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
    (env : Fin n → HF A) : closure (t.traced S p env).1 ⊆ (t.traced S p env).2 := by
  cases t with
  | var j => exact Finset.Subset.refl _
  | empty => exact Finset.Subset.refl _
  | atoms => exact Finset.Subset.refl _
  | pair a b =>
    intro z hz
    have hh := closure_double_subset _ _ hz
    simp only [Term.traced,Finset.mem_insert,Finset.mem_union] at hh ⊢
    rcases hh with he | ha | hb
    · exact Or.inl he
    · exact Or.inr (Or.inl (a.traced_closure S p env ha))
    · exact Or.inr (Or.inr (b.traced_closure S p env hb))
  | union a =>
    exact (closure_unionHF_subset _).trans (Finset.insert_subset_insert _ (a.traced_closure S p env))
  | unique a =>
    exact (closure_uniqueHF_subset _).trans (Finset.insert_subset_insert _ (a.traced_closure S p env))
  | card a => exact Finset.subset_union_left
  | comprehend body range guard =>
    simp only [Term.traced,closure_ofFinset]
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with he | hz
    · exact Finset.mem_insert.mpr (Or.inl he)
    apply Finset.mem_insert_of_mem
    obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,body.traced_closure S p _ hzy⟩)
  | iterate step =>
    exact tracedLoop_closure_subset p _ (fun x => step.traced_closure S p (Fin.cons x env)) _ _

lemma Term.traced_self (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
    (env : Fin n → HF A) : (t.traced S p env).1 ∈ (t.traced S p env).2 :=
  t.traced_closure S p env (mem_closure_self _)

mutual
  lemma Term.traced_closed (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
      (env : Fin n → HF A) : ClosedTrace (t.traced S p env).2 := by
    cases t with
    | var j => exact closedTrace_closure _
    | empty => exact closedTrace_closure _
    | atoms => exact closedTrace_closure _
    | pair a b =>
      exact closedTrace_insert (closedTrace_union (a.traced_closed S p env)
        (b.traced_closed S p env)) _ ((Term.pair a b).traced_closure S p env)
    | union a =>
      exact closedTrace_insert (a.traced_closed S p env) _ ((Term.union a).traced_closure S p env)
    | unique a =>
      exact closedTrace_insert (a.traced_closed S p env) _ ((Term.unique a).traced_closure S p env)
    | card a => exact closedTrace_union (closedTrace_closure _) (a.traced_closed S p env)
    | comprehend body range guard =>
      apply closedTrace_insert _ _ ((Term.comprehend body range guard).traced_closure S p env)
      exact closedTrace_union (closedTrace_union (range.traced_closed S p env)
        (closedTrace_biUnion _ _ (fun x _ => guard.traced_closed S p (Fin.cons x env))))
        (closedTrace_biUnion _ _ (fun x _ => body.traced_closed S p (Fin.cons x env)))
    | iterate step =>
      exact tracedLoop_closed p _ (fun x => step.traced_closed S p (Fin.cons x env)) _ _
  lemma Formula.traced_closed (S : Input A) (p : ℕ) {n : ℕ} (f : Formula n)
      (env : Fin n → HF A) : ClosedTrace (f.traced S p env).2 := by
    cases f with
    | equal a b | input r a b => exact closedTrace_union (a.traced_closed S p env) (b.traced_closed S p env)
    | neg a => exact a.traced_closed S p env
    | and a b | or a b => exact closedTrace_union (a.traced_closed S p env) (b.traced_closed S p env)
    | wsc step choice witness output => intro x hx; exact False.elim (Finset.notMem_empty _ hx)
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

variable {A : Type}

lemma closure_eq_insert_TC (x : HF A) : closure x = insert x (TC x) := by
  rw [Hereditary.closure]
  ext y
  simp only [TC,mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  constructor <;> rintro (h | ⟨a,ha,h⟩)
  · exact Or.inl h
  · exact Or.inr ⟨a,ha,h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a,ha,h⟩

lemma closure_card_le_TC (x : HF A) : (closure x).card ≤ (TC x).card+1 := by
  rw [closure_eq_insert_TC]
  exact card_insert_le _ _

lemma card_closure_atoms [Fintype A] :
    (closure (ofFinset (univ.image (atom (A := A))))).card ≤ Fintype.card A+1 := by
  have he : familyClosure (univ.image (atom (A := A))) = univ.image atom := by
    ext x
    simp only [familyClosure,mem_biUnion,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,h⟩
      rw [closure_atom] at h
      exact ⟨a,(Finset.mem_singleton.mp h).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨atom a,⟨a,rfl⟩,mem_closure_self _⟩
  have hh : closure (ofFinset (univ.image (atom (A := A)))) =
      insert (ofFinset (univ.image atom)) (univ.image atom) := by
    rw [closure_ofFinset,he]
    ext x
    simp only [mem_insert,mem_image,mem_univ,true_and]
  rw [hh]
  exact (card_insert_le _ _).trans (Nat.add_le_add_right
    (card_image_le.trans (by rw [card_univ])) 1)

lemma tracedLoop_card (p : ℕ) (step : HF A → Traced A (HF A)) (C : ℕ)
    (hs : ∀ x, (TC x).card ≤ p → (step x).2.card ≤ C) (fuel : ℕ) (x : HF A) :
    (tracedLoop p step fuel x).2.card ≤ fuel*C+1 := by
  induction fuel generalizing x with
  | zero => simp only [tracedLoop,closure_emptyHF,card_singleton,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs with hb he
    · change (step x).2.card ≤ (fuel+1)*C+1
      have hh := hs x hb
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · have hh := (card_union_le (step x).2 (tracedLoop p step fuel (step x).1).2).trans
        (add_le_add (hs x hb) (ih (step x).1))
      calc
        _ ≤ C + (fuel*C+1) := hh
        _ = (fuel+1)*C+1 := by ring
    · simp only [closure_emptyHF,card_singleton]
      omega

mutual
  def Term.traceBound : {n : ℕ} → Term n → Polynomial ℕ
    | _, .var _ => .X
    | _, .empty => 1
    | _, .atoms => .X
    | _, .pair a b => 1+a.traceBound+b.traceBound
    | _, .union a | _, .unique a => 1+a.traceBound
    | _, .card a => 1+2*a.traceBound
    | _, .comprehend body range guard => 1+range.traceBound+range.traceBound *
        (guard.traceBound.comp (.X+range.traceBound)+body.traceBound.comp (.X+range.traceBound))
    | _, .iterate step => 1+.X*(step.traceBound.comp (2*.X))
  def Formula.traceBound : {n : ℕ} → Formula n → Polynomial ℕ
    | _, .equal a b | _, .input _ a b => a.traceBound+b.traceBound
    | _, .neg a => a.traceBound
    | _, .and a b | _, .or a b => a.traceBound+b.traceBound
    | _, .wsc _ _ _ _ => 0
end

variable [Fintype A]

def tracePotential {n : ℕ} (p : ℕ) (env : Fin n → HF A) : ℕ :=
  Fintype.card A+p+1+∑ j, (closure (env j)).card

lemma tracePotential_var {n : ℕ} (p : ℕ) (env : Fin n → HF A) (j : Fin n) :
    (closure (env j)).card ≤ tracePotential p env := by
  unfold tracePotential
  exact (single_le_sum (f := fun j => (closure (env j)).card)
    (fun _ _ => Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left _ _)

lemma tracePotential_cons {n : ℕ} (p : ℕ) (env : Fin n → HF A) (x : HF A) :
    tracePotential p (Fin.cons x env) = tracePotential p env+(closure x).card := by
  simp only [tracePotential,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  omega

mutual
  lemma Term.traced_card_le (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
      (env : Fin n → HF A) (K : ℕ) (hK : tracePotential p env ≤ K) :
      (t.traced S p env).2.card ≤ t.traceBound.eval K := by
    cases t with
    | var j =>
      simpa only [Term.traced,Term.traceBound,Polynomial.eval_X] using (tracePotential_var p env j).trans hK
    | empty =>
      simp only [Term.traced,closure_emptyHF,card_singleton,Term.traceBound,Polynomial.eval_one,le_refl]
    | atoms =>
      have hk : Fintype.card A+1 ≤ K := by unfold tracePotential at hK; omega
      simpa only [Term.traced,Term.traceBound,Polynomial.eval_X] using card_closure_atoms.trans hk
    | pair a b =>
      have ha := a.traced_card_le S p env K hK
      have hb := b.traced_card_le S p env K hK
      have hh := (card_insert_le (double (a.traced S p env).1 (b.traced S p env).1)
        ((a.traced S p env).2 ∪ (b.traced S p env).2)).trans
        (Nat.add_le_add_right (card_union_le _ _) 1)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one]
      omega
    | union a | unique a =>
      have ha := a.traced_card_le S p env K hK
      have hh := card_insert_le (s := (a.traced S p env).2)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one]
      exact (hh _).trans (by omega)
    | card a =>
      have ha := a.traced_card_le S p env K hK
      have hc : (closure (cardHF (a.traced S p env).1)).card ≤ a.traceBound.eval K+1 := by
        rw [cardHF,card_closure_ordinal]
        exact Nat.add_le_add_right ((card_le_card ((elements_subset_closure _).trans
          (a.traced_closure S p env))).trans ha) 1
      have hh := (card_union_le _ _).trans (add_le_add hc ha)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_ofNat]
      exact hh.trans (by omega)
    | comprehend body range guard =>
      have hr := range.traced_card_le S p env K hK
      have hc : (elements (range.traced S p env).1).card ≤ range.traceBound.eval K :=
        (card_le_card ((elements_subset_closure _).trans (range.traced_closure S p env))).trans hr
      have hen (x) (hx : x ∈ elements (range.traced S p env).1) :
          tracePotential p (Fin.cons x env) ≤ K+range.traceBound.eval K := by
        rw [tracePotential_cons]
        exact add_le_add hK ((card_le_card ((closure_member_subset hx).trans
          (range.traced_closure S p env))).trans hr)
      let E := elements (range.traced S p env).1
      let D := E.filter (fun x => (guard.traced S p (Fin.cons x env)).1 = true)
      have hg : (E.biUnion fun x => (guard.traced S p (Fin.cons x env)).2).card ≤
          range.traceBound.eval K*guard.traceBound.eval (K+range.traceBound.eval K) := by
        apply card_biUnion_le.trans
        apply (sum_le_card_nsmul E _ _ (fun x hx => guard.traced_card_le S p _ _ (hen x hx))).trans
        simpa only [nsmul_eq_mul,Nat.cast_id] using Nat.mul_le_mul_right _ hc
      have hb : (D.biUnion fun x => (body.traced S p (Fin.cons x env)).2).card ≤
          range.traceBound.eval K*body.traceBound.eval (K+range.traceBound.eval K) := by
        apply card_biUnion_le.trans
        apply (sum_le_card_nsmul D _ _ (fun x hx => body.traced_card_le S p _ _
          (hen x (mem_filter.mp hx).1))).trans
        simpa only [nsmul_eq_mul,Nat.cast_id] using
          Nat.mul_le_mul_right _ ((card_le_card (filter_subset _ _)).trans hc)
      have hh := (card_insert_le (s := (range.traced S p env).2 ∪
        (E.biUnion fun x => (guard.traced S p (Fin.cons x env)).2) ∪
        (D.biUnion fun x => (body.traced S p (Fin.cons x env)).2))
        (ofFinset (D.image fun x => (body.traced S p (Fin.cons x env)).1))).trans
        (Nat.add_le_add_right ((card_union_le _ _).trans
          (add_le_add ((card_union_le _ _).trans (add_le_add hr hg)) hb)) 1)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X]
      change (insert _ ((range.traced S p env).2 ∪ _ ∪ _)).card ≤ _ at hh
      exact hh.trans (by ring_nf; omega)
    | iterate step =>
      have hk : p+1 ≤ K := by unfold tracePotential at hK; omega
      have hb := tracedLoop_card p (fun x => step.traced S p (Fin.cons x env))
        (step.traceBound.eval (2*K)) (fun x hx => step.traced_card_le S p _ _ (by
          rw [tracePotential_cons]
          have hc := (closure_card_le_TC x).trans (Nat.add_le_add_right hx 1)
          omega)) (p+1) emptyHF
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat]
      exact hb.trans (by nlinarith [Nat.mul_le_mul_right (step.traceBound.eval (2*K)) hk])
  lemma Formula.traced_card_le (S : Input A) (p : ℕ) {n : ℕ} (f : Formula n)
      (env : Fin n → HF A) (K : ℕ) (hK : tracePotential p env ≤ K) :
      (f.traced S p env).2.card ≤ f.traceBound.eval K := by
    cases f with
    | equal a b | input r a b =>
      simp only [Formula.traced,Formula.traceBound,Polynomial.eval_add]
      exact (card_union_le _ _).trans (add_le_add (a.traced_card_le S p env K hK)
        (b.traced_card_le S p env K hK))
    | neg a => exact a.traced_card_le S p env K hK
    | and a b | or a b =>
      simp only [Formula.traced,Formula.traceBound,Polynomial.eval_add]
      exact (card_union_le _ _).trans (add_le_add (a.traced_card_le S p env K hK)
        (b.traced_card_le S p env K hK))
    | wsc step choice witness output => simp only [Formula.traced,Formula.traceBound,Polynomial.eval_zero,card_empty,le_refl]
end

end

end WitnessedChoice.BGS

end

end OAI
