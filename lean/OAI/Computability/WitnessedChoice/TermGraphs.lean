import OAI.Computability.WitnessedChoice.ChoiceTrace

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

variable {A : Type}

def LoopGraph (d : Set (HF A)) (p : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop) :
    ℕ → Domain d → Domain d → (Fin n → Domain d) → Prop
  | 0, z, _, _ => z.val = emptyHF
  | fuel+1, z, x, env =>
      ((TC x.val).card > p ∧ z.val = emptyHF) ∨
      ((TC x.val).card ≤ p ∧ ∃ y : Domain d, step y (Fin.cons x env) ∧
        ((x = y ∧ z = x) ∨ (x ≠ y ∧ LoopGraph d p step fuel z y env)))

mutual
  def Term.Graph [Fintype A] (d : Set (HF A)) (S : Input A) (p K : ℕ) :
      {n : ℕ} → Term n → Domain d → (Fin n → Domain d) → Prop
    | _, .var j, z, env => z = env j
    | _, .empty, z, _ => z.val = emptyHF
    | _, .atoms, z, _ => z.val = ofFinset (Finset.univ.image atom)
    | _, .pair a b, z, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ z.val = double x.val y.val
    | _, .union a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧ z.val = unionHF x.val
    | _, .unique a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧ z.val = uniqueHF x.val
    | _, .card a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧
        (elements x.val).card ≤ K ∧ z.val = cardHF x.val
    | _, .comprehend body range guard, z, env => ∃ r : Domain d,
        range.Graph d S p K r env ∧
        (∀ x : Domain d, x.val ∈ r.val → ∃ b : Bool,
          guard.Graph d S p K b (Fin.cons x env) ∧
            (b = true → ∃ y : Domain d, body.Graph d S p K y (Fin.cons x env))) ∧
        isSet z.val = true ∧ ∀ y : Domain d, y.val ∈ z.val ↔ ∃ x : Domain d,
          x.val ∈ r.val ∧ guard.Graph d S p K true (Fin.cons x env) ∧
            body.Graph d S p K y (Fin.cons x env)
    | _, .iterate step, z, env => ∃ x : Domain d, x.val = emptyHF ∧
        LoopGraph d p (step.Graph d S p K) (p+1) z x env
  def Formula.Graph [Fintype A] (d : Set (HF A)) (S : Input A) (p K : ℕ) :
      {n : ℕ} → Formula n → Bool → (Fin n → Domain d) → Prop
    | _, .equal a b, v, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ v = decide (x.val = y.val)
    | _, .input r a b, v, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ v = inputHF S r x.val y.val
    | _, .neg a, v, env => ∃ b : Bool, a.Graph d S p K b env ∧ v = !b
    | _, .and a b, v, env => ∃ c e : Bool, a.Graph d S p K c env ∧
        b.Graph d S p K e env ∧ v = (c && e)
    | _, .or a b, v, env => ∃ c e : Bool, a.Graph d S p K c env ∧
        b.Graph d S p K e env ∧ v = (c || e)
    | _, .wsc _ _ _ _, _, _ => False
end

lemma domain_cons_val {d : Set (HF A)} {n : ℕ} (x : Domain d) (env : Fin n → Domain d) :
    (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val) = Fin.cons x.val (fun j => (env j).val) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

lemma LoopGraph.sound {d : Set (HF A)} (p : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop)
    (ts : HF A → Traced A (HF A)) (env : Fin n → Domain d)
    (hs : ∀ x y : Domain d, step y (Fin.cons x env) → y.val = (ts x.val).1)
    (fuel : ℕ) (z x : Domain d) (h : LoopGraph d p step fuel z x env) :
    z.val = (tracedLoop p ts fuel x.val).1 := by
  induction fuel generalizing z x with
  | zero => exact h
  | succ fuel ih =>
    rcases h with ⟨hb,hz⟩ | ⟨hb,y,hy,he⟩
    · simpa only [tracedLoop,ite_eq_right (by omega : ¬ (TC x.val).card ≤ p)] using hz
    · have hval := hs x y hy
      rcases he with ⟨rfl,rfl⟩ | ⟨hne,hrec⟩
      · simp only [tracedLoop,ite_eq_left hb,ite_eq_left hval]
      · have hn : x.val ≠ (ts x.val).1 := fun h => hne (Subtype.ext (h.trans hval.symm))
        simp only [tracedLoop,ite_eq_left hb,ite_eq_right hn]
        rw [← hval]
        exact ih z y hrec

variable [Fintype A]

mutual
  lemma Term.graph_sound (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {n : ℕ}
      (t : Term n) (z : Domain d) (env : Fin n → Domain d)
      (h : t.Graph d S p K z env) : z.val = (t.traced S p (fun j => (env j).val)).1 := by
    cases t with
    | var j => exact congrArg Subtype.val h
    | empty => exact h
    | atoms => exact h
    | pair a b =>
      obtain ⟨x,y,hx,hy,hz⟩ := h
      change z.val = double (a.traced S p (fun j => (env j).val)).1
        (b.traced S p (fun j => (env j).val)).1
      exact hz.trans (congrArg₂ double (a.graph_sound d S p K hd x env hx)
        (b.graph_sound d S p K hd y env hy))
    | union a =>
      obtain ⟨x,hx,hz⟩ := h
      exact hz.trans (congrArg unionHF (a.graph_sound d S p K hd x env hx))
    | unique a =>
      obtain ⟨x,hx,hz⟩ := h
      exact hz.trans (congrArg uniqueHF (a.graph_sound d S p K hd x env hx))
    | card a =>
      obtain ⟨x,hx,_,hz⟩ := h
      exact hz.trans (congrArg cardHF (a.graph_sound d S p K hd x env hx))
    | comprehend body range guard =>
      obtain ⟨r,hr,hall,hz,hmem⟩ := h
      have her := range.graph_sound d S p K hd r env hr
      apply ext_sets hz (isSet_ofFinset _)
      intro y
      simp only [mem_ofFinset,Finset.mem_image,Finset.mem_filter]
      constructor
      · intro hy
        obtain ⟨x,hx,hg,hb⟩ := (hmem ⟨y,hd _ z.property _ hy⟩).mp hy
        refine ⟨x.val,⟨by rwa [← her],?_⟩,?_⟩
        · have hh := guard.graph_sound d S p K hd true (Fin.cons x env) hg
          simpa only [domain_cons_val] using hh.symm
        · have hh := body.graph_sound d S p K hd ⟨y,hd _ z.property _ hy⟩ (Fin.cons x env) hb
          simpa only [domain_cons_val] using hh.symm
      · rintro ⟨x,⟨hxr,hgt⟩,hey⟩
        have hxd : x ∈ d := hd _ r.property _ (by rwa [her])
        let xx : Domain d := ⟨x,hxd⟩
        have hxx : xx.val ∈ r.val := by change x ∈ r.val; rwa [her]
        obtain ⟨v,hv,hbody⟩ := hall xx hxx
        have he := guard.graph_sound d S p K hd v (Fin.cons xx env) hv
        simp only [domain_cons_val] at he
        have hvt : v = true := he.trans hgt
        obtain ⟨w,hw⟩ := hbody hvt
        have hew := body.graph_sound d S p K hd w (Fin.cons xx env) hw
        simp only [domain_cons_val] at hew
        have hwval : w.val = y := hew.trans hey
        have hyd : y ∈ d := hwval ▸ w.property
        apply (hmem ⟨y,hyd⟩).mpr
        refine ⟨xx,hxx,hvt ▸ hv,?_⟩
        have heq : w = (⟨y,hyd⟩ : Domain d) := Subtype.ext hwval
        rwa [← heq]
    | iterate step =>
      obtain ⟨x,hx,hl⟩ := h
      have hh := LoopGraph.sound p (step.Graph d S p K)
        (fun y => step.traced S p (Fin.cons y (fun j => (env j).val))) env
        (fun x y h => by simpa only [domain_cons_val] using
          step.graph_sound d S p K hd y (Fin.cons x env) h) (p+1) z x hl
      simpa only [Term.traced,hx] using hh
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.graph_sound (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {n : ℕ}
      (f : Formula n) (v : Bool) (env : Fin n → Domain d)
      (h : f.Graph d S p K v env) : v = (f.traced S p (fun j => (env j).val)).1 := by
    cases f with
    | equal a b =>
      obtain ⟨x,y,hx,hy,hv⟩ := h
      exact hv.trans (congrArg₂ (fun x y : HF A => decide (x = y))
        (a.graph_sound d S p K hd x env hx) (b.graph_sound d S p K hd y env hy))
    | input r a b =>
      obtain ⟨x,y,hx,hy,hv⟩ := h
      exact hv.trans (congrArg₂ (inputHF S r)
        (a.graph_sound d S p K hd x env hx) (b.graph_sound d S p K hd y env hy))
    | neg a =>
      obtain ⟨b,hb,hv⟩ := h
      change v = !(a.traced S p (fun j => (env j).val)).1
      exact hv.trans (congrArg Bool.not (a.graph_sound d S p K hd b env hb))
    | and a b =>
      obtain ⟨c,e,hc,he,hv⟩ := h
      exact hv.trans (congrArg₂ Bool.and (a.graph_sound d S p K hd c env hc)
        (b.graph_sound d S p K hd e env he))
    | or a b =>
      obtain ⟨c,e,hc,he,hv⟩ := h
      exact hv.trans (congrArg₂ Bool.or (a.graph_sound d S p K hd c env hc)
        (b.graph_sound d S p K hd e env he))
    | wsc step choice witness output => exact h.elim
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

variable {A : Type}

def AdmissibleTrace (d : Set (HF A)) (K : ℕ) (F : Finset (HF A)) : Prop :=
  ∀ x ∈ F, x ∈ d ∧ (elements x).card ≤ K

lemma AdmissibleTrace.mono {d : Set (HF A)} {K : ℕ} {F G : Finset (HF A)}
    (h : AdmissibleTrace d K F) (hg : G ⊆ F) : AdmissibleTrace d K G :=
  fun x hx => h x (hg hx)

lemma admissibleTrace_of_closed {F : Finset (HF A)} (hF : ClosedTrace F) :
    AdmissibleTrace (F : Set (HF A)) F.card F := by
  intro x hx
  exact ⟨hx,Finset.card_le_card ((elements_subset_closure x).trans (hF x hx))⟩

lemma LoopGraph.complete {d : Set (HF A)} (p K : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop)
    (ts : HF A → Traced A (HF A)) (env : Fin n → Domain d)
    (hout : ∀ x, (ts x).1 ∈ (ts x).2)
    (hs : ∀ x y : Domain d, AdmissibleTrace d K (ts x.val).2 →
      y.val = (ts x.val).1 → step y (Fin.cons x env))
    (fuel : ℕ) (z x : Domain d)
    (ht : AdmissibleTrace d K (tracedLoop p ts fuel x.val).2)
    (hz : z.val = (tracedLoop p ts fuel x.val).1) :
    LoopGraph d p step fuel z x env := by
  induction fuel generalizing z x with
  | zero => exact hz
  | succ fuel ih =>
    by_cases hb : (TC x.val).card ≤ p
    · have htstep : AdmissibleTrace d K (ts x.val).2 := by
        simp only [tracedLoop,ite_eq_left hb] at ht
        split_ifs at ht with he
        · exact ht
        · exact ht.mono Finset.subset_union_left
      let y : Domain d := ⟨(ts x.val).1,(htstep _ (hout _)).1⟩
      refine Or.inr ⟨hb,y,hs x y htstep rfl,?_⟩
      by_cases he : x.val = (ts x.val).1
      · left
        exact ⟨Subtype.ext he,Subtype.ext (by simpa only [tracedLoop,ite_eq_left hb,ite_eq_left he] using hz)⟩
      · right
        refine ⟨fun h => he (congrArg Subtype.val h),?_⟩
        apply ih z y
        · exact ht.mono (by simp only [tracedLoop,ite_eq_left hb,ite_eq_right he]; exact Finset.subset_union_right)
        · simpa only [tracedLoop,ite_eq_left hb,ite_eq_right he] using hz
    · exact Or.inl ⟨by omega,by simpa only [tracedLoop,ite_eq_right hb] using hz⟩

variable [Fintype A]

mutual
  lemma Term.graph_complete (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) (hempty : emptyHF ∈ d) {n : ℕ} (t : Term n) (hzero : t.wscCount = 0)
      (z : Domain d) (env : Fin n → Domain d)
      (ht : AdmissibleTrace d K (t.traced S p (fun j => (env j).val)).2)
      (hz : z.val = (t.traced S p (fun j => (env j).val)).1) : t.Graph d S p K z env := by
    cases t with
    | var j => exact Subtype.ext hz
    | empty => exact hz
    | atoms => exact hz
    | pair a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have ha := ht.mono (Finset.subset_union_left.trans (Finset.subset_insert _ _))
      have hb := ht.mono (Finset.subset_union_right.trans (Finset.subset_insert _ _))
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      let y : Domain d := ⟨(b.traced S p (fun j => (env j).val)).1,(hb _ (b.traced_self S p _)).1⟩
      exact ⟨x,y,a.graph_complete d S p K hd hempty h.1 x env ha rfl,
        b.graph_complete d S p K hd hempty h.2 y env hb rfl,hz⟩
    | union a | unique a =>
      have ha := ht.mono (Finset.subset_insert _ _)
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      exact ⟨x,a.graph_complete d S p K hd hempty hzero x env ha rfl,hz⟩
    | card a =>
      have ha := ht.mono Finset.subset_union_right
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      exact ⟨x,a.graph_complete d S p K hd hempty hzero x env ha rfl,
        (ha _ (a.traced_self S p _)).2,hz⟩
    | comprehend body range guard =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have h' := Nat.add_eq_zero_iff.mp h.1
      have hr := ht.mono (Finset.subset_union_left.trans
        (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
      let r : Domain d := ⟨(range.traced S p (fun j => (env j).val)).1,
        (hr _ (range.traced_self S p _)).1⟩
      have hg (x : Domain d) (hx : x.val ∈ r.val) :
          AdmissibleTrace d K (guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).2 := by
        rw [domain_cons_val]
        apply ht.mono
        intro y hy
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x.val,hx,hy⟩)))
      have hb (x : Domain d) (hx : x.val ∈ r.val)
          (hxg : (guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1 = true) :
          AdmissibleTrace d K (body.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).2 := by
        rw [domain_cons_val] at hxg ⊢
        apply ht.mono
        intro y hy
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨x.val,Finset.mem_filter.mpr ⟨hx,hxg⟩,hy⟩))
      refine ⟨r,range.graph_complete d S p K hd hempty h'.2 r env hr rfl,?_,?_,?_⟩
      · intro x hx
        refine ⟨(guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1,
          guard.graph_complete d S p K hd hempty h.2 _ _ (hg x hx) rfl,?_⟩
        intro hxg
        let y : Domain d := ⟨(body.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1,
          ((hb x hx hxg) _ (body.traced_self S p _)).1⟩
        exact ⟨y,body.graph_complete d S p K hd hempty h'.1 y _ (hb x hx hxg) rfl⟩
      · rw [hz]; exact isSet_ofFinset _
      · intro y
        rw [hz]
        change y.val ∈ ofFinset _ ↔ _
        simp only [mem_ofFinset,Finset.mem_image,Finset.mem_filter]
        constructor
        · rintro ⟨x,⟨hx,hxg⟩,hy⟩
          have hxd : x ∈ d := (hr x (range.traced_closure S p _ (elements_subset_closure _ hx))).1
          let xx : Domain d := ⟨x,hxd⟩
          have hxg' : (guard.traced S p (fun j => ((Fin.cons xx env : Fin (_+1) → Domain d) j).val)).1 = true := by
            simpa only [domain_cons_val] using hxg
          refine ⟨xx,hx,guard.graph_complete d S p K hd hempty h.2 true _ (hg xx hx) hxg'.symm,?_⟩
          apply body.graph_complete d S p K hd hempty h'.1 y _ (hb xx hx hxg')
          simpa only [domain_cons_val] using hy.symm
        · rintro ⟨x,hx,hxg,hy⟩
          have hgt := guard.graph_sound d S p K hd true (Fin.cons x env) hxg
          have hbt := body.graph_sound d S p K hd y (Fin.cons x env) hy
          simp only [domain_cons_val] at hgt hbt
          exact ⟨x.val,⟨hx,hgt.symm⟩,hbt.symm⟩
    | iterate step =>
      let x : Domain d := ⟨emptyHF,hempty⟩
      refine ⟨x,rfl,LoopGraph.complete p K (step.Graph d S p K)
        (fun y => step.traced S p (Fin.cons y (fun j => (env j).val))) env
        (fun y => step.traced_self S p _) ?_ (p+1) z x ht hz⟩
      intro a b ha hb
      apply step.graph_complete d S p K hd hempty hzero b (Fin.cons a env)
      · simpa only [domain_cons_val] using ha
      · simpa only [domain_cons_val] using hb
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.graph_complete (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) (hempty : emptyHF ∈ d) {n : ℕ} (f : Formula n) (hzero : f.wscCount = 0)
      (v : Bool) (env : Fin n → Domain d)
      (ht : AdmissibleTrace d K (f.traced S p (fun j => (env j).val)).2)
      (hv : v = (f.traced S p (fun j => (env j).val)).1) : f.Graph d S p K v env := by
    cases f with
    | equal a b | input r a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have ha := ht.mono Finset.subset_union_left
      have hb := ht.mono Finset.subset_union_right
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      let y : Domain d := ⟨(b.traced S p (fun j => (env j).val)).1,(hb _ (b.traced_self S p _)).1⟩
      exact ⟨x,y,a.graph_complete d S p K hd hempty h.1 x env ha rfl,
        b.graph_complete d S p K hd hempty h.2 y env hb rfl,hv⟩
    | neg a => exact ⟨_,a.graph_complete d S p K hd hempty hzero _ env ht rfl,hv⟩
    | and a b | or a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      exact ⟨_,_,a.graph_complete d S p K hd hempty h.1 _ env (ht.mono Finset.subset_union_left) rfl,
        b.graph_complete d S p K hd hempty h.2 _ env (ht.mono Finset.subset_union_right) rfl,hv⟩
    | wsc step choice witness output => simp only [Formula.wscCount] at hzero; omega
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

variable {ι R : Type} {D : ι → Type} {S : ∀ i, Counting.Structure R (D i)} {m n : ℕ}

lemma uniform_const (P : Prop) : UniformDefinable S m n (fun _ _ => P) := by
  by_cases h : P
  · exact UniformDefinable.falsum.neg.congr (fun _ _ => by simp [h])
  · exact UniformDefinable.falsum.congr (fun _ _ => by simp [h])

lemma uniform_exists_finite {X : Type} [Fintype X] {P : X → ∀ i, (Fin n → D i) → Prop}
    (h : ∀ x, UniformDefinable S m n (P x)) :
    UniformDefinable S m n (fun i v => ∃ x, P x i v) := by
  simpa only [Finset.mem_univ,true_and] using
    UniformDefinable.exists_finset Finset.univ (fun x _ => h x)

lemma uniform_decide {P : ∀ i, (Fin n → D i) → Prop}
    (h : UniformDefinable S m n P) (b : Bool) :
    UniformDefinable S m n (fun i v => b = decide (P i v)) := by
  cases b
  · exact h.neg.congr (fun _ _ => by simp)
  · exact h.congr (fun _ _ => by simp)

lemma uniform_formula_binary
    {P Q : ∀ i, (Fin (n+1) → D i) → Prop} {T : ∀ i, (Fin 2 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q)
    (hT : UniformDefinable S m 2 T) (hr : n+1 < m) :
    UniformDefinable S m n (fun i v => ∃ x y,
      P i (Fin.cons x v) ∧ Q i (Fin.cons y v) ∧ T i ![x,y]) := by
  have h1 := hP.reindex (Fin.cons 1 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h2 := hQ.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h3 := hT.reindex (![1,0] : Fin 2 → Fin (n+2))
  apply (((h1.and (h2.and h3)).ex hr).ex (by omega)).congr
  intro i v
  apply exists_congr; intro x
  apply exists_congr; intro y
  have h1' : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 1 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) = Fin.cons x v := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  have h2' : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) = Fin.cons y v := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  have h3' : Fin.cons y (Fin.cons x v) ∘ (![1,0] : Fin 2 → Fin (n+2)) = ![x,y] := by
    funext j; fin_cases j <;> rfl
  simp only [h1',h2',h3']

variable {A : ι → Type} (d : ∀ i, Set (HF (A i)))

variable (T : ∀ i, Counting.Structure R (Domain (d i)))

variable (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))

include hmem hset in
lemma uniform_BGS_comprehension
    {P : ∀ i, Domain (d i) → (Fin n → Domain (d i)) → Prop}
    {Q : ∀ i, Bool → (Fin (n+1) → Domain (d i)) → Prop}
    {B : ∀ i, Domain (d i) → (Fin (n+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable T m (n+1) (fun i v => P i (v 0) (Fin.tail v)))
    (hQ : ∀ b, UniformDefinable T m (n+1) (fun i v => Q i b v))
    (hB : UniformDefinable T m (n+2) (fun i v => B i (v 0) (Fin.tail v)))
    (hm : n+4 ≤ m) : UniformDefinable T m (n+1) (fun i v => ∃ r,
      P i r (Fin.tail v) ∧
      (∀ x : Domain (d i), x.val ∈ r.val → ∃ b : Bool,
        Q i b (Fin.cons x (Fin.tail v)) ∧
          (b = true → ∃ y : Domain (d i), B i y (Fin.cons x (Fin.tail v)))) ∧
      isSet (v 0).val = true ∧ ∀ y : Domain (d i), y.val ∈ (v 0).val ↔
        ∃ x : Domain (d i), x.val ∈ r.val ∧ Q i true (Fin.cons x (Fin.tail v)) ∧
          B i y (Fin.cons x (Fin.tail v))) := by
  have hBtotal := (hB.reindex
    (Fin.cons 0 (Fin.cons 1 (fun j => j.succ.succ.succ.succ)) : Fin (n+2) → Fin (n+4))).ex (by omega)
  have htotal := ((hmem.reindex (![0,1] : Fin 2 → Fin (n+3))).imp
    (uniform_exists_finite (fun b : Bool =>
      ((hQ b).reindex (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))).and
        ((uniform_const (b = true)).imp hBtotal)))).all (by omega)
  have hguard := (hQ true).reindex
    (Fin.cons 0 (fun j => j.succ.succ.succ.succ) : Fin (n+1) → Fin (n+4))
  have hbody := hB.reindex
    (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ.succ)) : Fin (n+2) → Fin (n+4))
  have hrhs := ((hmem.reindex (![0,2] : Fin 2 → Fin (n+4))).and (hguard.and hbody)).ex (by omega)
  have hext := ((hmem.reindex (![0,2] : Fin 2 → Fin (n+3))).iff hrhs).all (by omega)
  have hbound := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have hset' := hset.reindex (![1] : Fin 1 → Fin (n+2))
  apply ((hbound.and (htotal.and (hset'.and hext))).ex (by omega)).congr
  intro i v
  simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
  rfl

lemma LoopGraph.uniform (p : ℕ)
    (step : ∀ i, Domain (d i) → (Fin (n+1) → Domain (d i)) → Prop)
    (hstep : UniformDefinable T m (n+2) (fun i v => step i (v 0) (Fin.tail v)))
    (hcut : UniformDefinable T m 1 (fun _ v => (TC (v 0).val).card ≤ p))
    (hemp : UniformDefinable T m 1 (fun _ v => (v 0).val = emptyHF))
    (hm : n+2 < m) (fuel : ℕ) : UniformDefinable T m (n+2)
      (fun i v => LoopGraph (d i) p (step i) fuel (v 0) (v 1) (Fin.tail (Fin.tail v))) := by
  induction fuel with
  | zero => exact hemp.reindex ![0]
  | succ fuel ih =>
    have hc := hcut.reindex (![1] : Fin 1 → Fin (n+2))
    have hz := hemp.reindex (![0] : Fin 1 → Fin (n+2))
    have hs := hstep.reindex (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3))
    have hxy : UniformDefinable T m (n+3) (fun _ v => v 2 = v 0) := UniformDefinable.equal 2 0
    have hzx : UniformDefinable T m (n+3) (fun _ v => v 1 = v 2) := UniformDefinable.equal 1 2
    have hrec := ih.reindex (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3))
    have hy := (hs.and ((hxy.and hzx).or (hxy.neg.and hrec))).ex hm
    apply ((hc.neg.and hz).or (hc.and hy)).congr
    intro i v
    have hvc : v ∘ (![1] : Fin 1 → Fin (n+2)) = ![v 1] := by
      funext j; fin_cases j; rfl
    have hvz : v ∘ (![0] : Fin 1 → Fin (n+2)) = ![v 0] := by
      funext j; fin_cases j; rfl
    have hs' (y : Domain (d i)) : Fin.cons y v ∘
        (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3)) =
        Fin.cons y (Fin.cons (v 1) (Fin.tail (Fin.tail v))) := by
      funext j; refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun _ => rfl) j
    have hr' (y : Domain (d i)) : Fin.cons y v ∘
        (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3)) =
        Fin.cons (v 0) (Fin.cons y (Fin.tail (Fin.tail v))) := by
      funext j; refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun _ => rfl) j
    simp only [hvc,hvz,hs',hr',Fin.cons_zero,Fin.tail_cons]
    simp only [LoopGraph,not_le]
    rfl

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

lemma unionHF_eq_operational {A : Type} (x : HF A) : unionHF x = Operational.unionHF x := by
  unfold unionHF Operational.unionHF
  congr 1
  ext y
  simp only [Finset.mem_biUnion]

lemma uniqueHF_eq_operational {A : Type} (x : HF A) : uniqueHF x = Operational.uniqueHF x := rfl

lemma cardHF_eq_operational {A : Type} (x : HF A) : cardHF x = Operational.cardinalityHF x := rfl

lemma atomsHF_eq_operational {A : Type} [Fintype A] :
    ofFinset (Finset.univ.image (atom (A := A))) = (Operational.allAtoms : HF A) := by
  unfold Operational.allAtoms
  congr 1
  ext y
  simp only [Finset.mem_image]

mutual
  def Term.graphWidth : {n : ℕ} → Term n → ℕ
    | n, .var _ | n, .empty | n, .atoms => n+8
    | n, .pair a b => n+8+a.graphWidth+b.graphWidth
    | n, .union a | n, .unique a | n, .card a => n+8+a.graphWidth
    | n, .comprehend b r g => n+8+b.graphWidth+r.graphWidth+g.graphWidth
    | n, .iterate step => n+8+step.graphWidth
  def Formula.graphWidth : {n : ℕ} → Formula n → ℕ
    | n, .equal a b | n, .input _ a b => n+8+a.graphWidth+b.graphWidth
    | n, .neg a => n+8+a.graphWidth
    | n, .and a b | n, .or a b => n+8+a.graphWidth+b.graphWidth
    | n, .wsc _ _ _ _ => n+8
end

variable {ι R : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))

variable (S : ∀ i, Input (A i))

variable (hinput : ∀ r, UniformDefinable T m 2
    (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val))

mutual
  lemma Term.uniform_graph (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i)))
      (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
      (hp : ∀ i k, ordinal (A := A i) k ∈ d i)
      (ha : ∀ i a, atom a ∈ d i)
      (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))
      (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))
      (S : ∀ i, Input (A i))
      (hinput : ∀ r, UniformDefinable T m 2
        (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val)) (p K : ℕ) {n : ℕ} (t : Term n) (hm : t.graphWidth ≤ m) :
      UniformDefinable T m (n+1) (fun i v => t.Graph (d i) (S i) p K (v 0) (Fin.tail v)) := by
    cases t with
    | var j => exact UniformDefinable.equal 0 j.succ
    | empty =>
      simp only [Term.graphWidth] at hm
      exact (HFCoding.uniform_ordinal T hmem hset (by omega) hd hp 0).reindex ![0]
    | atoms =>
      simp only [Term.graphWidth] at hm
      apply ((Operational.uniform_atoms d T hd ha hmem hset (by omega)).reindex ![0]).congr
      intro i v
      simp only [Term.Graph,atomsHF_eq_operational,Function.comp_apply]
      rfl
    | pair a b =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (b.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_double_value d T hd hmem hset (by omega)) (by omega)
    | union a =>
      simp only [Term.graphWidth] at hm
      have hh := UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_union d T hd hmem hset (by omega)) (by omega : n+1 < m)
      apply hh.congr
      intro i v
      simp only [Term.Graph,unionHF_eq_operational,Fin.cons_zero,Fin.tail_cons]
      rfl
    | unique a =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_unique d T hd hp hmem hset (by omega)) (by omega)
    | card a =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_card d T hd hp hmem hset (by omega) K) (by omega)
    | comprehend body range guard =>
      simp only [Term.graphWidth] at hm
      exact uniform_BGS_comprehension d T hmem hset
        (range.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (fun b => guard.uniform_graph d T hd hp ha hmem hset S hinput p K b (by omega))
        (body.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega)) (by omega)
    | iterate step =>
      simp only [Term.graphWidth] at hm
      have hs := step.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega)
      have hc := uniform_TC_bound d T hd hmem (by omega) p
      have he : UniformDefinable T m 1 (fun _ v => (v 0).val = emptyHF) :=
        HFCoding.uniform_ordinal T hmem hset (by omega) hd hp 0
      have hl := (LoopGraph.uniform d T p (fun i => step.Graph (d i) (S i) p K)
        hs hc he (by omega : n+2 < m) (p+1)).reindex
          (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ)) : Fin (n+2) → Fin (n+2))
      apply (((he.reindex (![0] : Fin 1 → Fin (n+2))).and hl).ex (by omega)).congr
      intro i v
      simp only [Term.Graph,Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
      rfl
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.uniform_graph (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i)))
      (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
      (hp : ∀ i k, ordinal (A := A i) k ∈ d i)
      (ha : ∀ i a, atom a ∈ d i)
      (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))
      (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))
      (S : ∀ i, Input (A i))
      (hinput : ∀ r, UniformDefinable T m 2
        (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val)) (p K : ℕ) {n : ℕ} (f : Formula n) (b : Bool)
      (hm : f.graphWidth ≤ m) :
      UniformDefinable T m n (fun i v => f.Graph (d i) (S i) p K b v) := by
    cases f with
    | equal a c =>
      simp only [Formula.graphWidth] at hm
      have he : UniformDefinable T m 2 (fun _ v => (v 0).val = (v 1).val) :=
        (UniformDefinable.equal 0 1).congr (fun _ _ => Subtype.ext_iff)
      apply (uniform_formula_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (c.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (uniform_decide he b) (by omega : n+1 < m)).congr
      intro i v
      simp only [Formula.Graph,Fin.cons_zero,Fin.tail_cons]
      apply exists_congr; intro x
      apply exists_congr; intro y
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      apply and_congr_right; intro _
      apply and_congr_right; intro _
      apply Iff.of_eq
      apply congrArg (fun z : Bool => b = z)
      exact decide_eq_decide.mpr Iff.rfl
    | input r a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_formula_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (c.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (uniform_decide (hinput r) b) (by omega)
    | neg a =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun c : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K c (by omega)).and
          (uniform_const (b = !c)))
    | and a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun x : Bool => uniform_exists_finite (fun y : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K x (by omega)).and
          ((c.uniform_graph d T hd hp ha hmem hset S hinput p K y (by omega)).and
            (uniform_const (b = (x && y))))))
    | or a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun x : Bool => uniform_exists_finite (fun y : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K x (by omega)).and
          ((c.uniform_graph d T hd hp ha hmem hset S hinput p K y (by omega)).and
            (uniform_const (b = (x || y))))))
    | wsc step choice witness output => exact UniformDefinable.falsum
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

open WitnessedSeparation.Operational (lift lift_elements lift_ofFinset lift_empty lift_double)

variable {A B : Type}

lemma lift_emptyHF (e : A ≃ B) : lift e emptyHF = emptyHF := Operational.lift_empty e

lemma lift_unionHF (e : A ≃ B) (x : HF A) : lift e (unionHF x) = unionHF (lift e x) := by
  simpa only [unionHF_eq_operational] using Operational.lift_union e x

lemma lift_uniqueHF (e : A ≃ B) (x : HF A) : lift e (uniqueHF x) = uniqueHF (lift e x) :=
  Operational.lift_unique e x

lemma lift_cardHF (e : A ≃ B) (x : HF A) : lift e (cardHF x) = cardHF (lift e x) :=
  Operational.lift_card e x

lemma lift_atomsHF [Fintype A] [Fintype B] (e : A ≃ B) :
    lift e (ofFinset (univ.image (atom (A := A)))) = ofFinset (univ.image atom) := by
  simpa only [atomsHF_eq_operational] using Operational.lift_allAtoms e

lemma lift_inputHF (e : A ≃ B) (S : Input A) (T : Input B)
    (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (r : Symbol) (x y : HF A) :
    inputHF T r (lift e x) (lift e y) = inputHF S r x y := by
  apply Bool.eq_iff_iff.mpr
  simpa only [inputHF,decide_eq_true_eq,Operational.inputRelation] using
    Operational.lift_input e S.rel T.rel h r x y

variable [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma lift_closureHF (e : A ≃ B) (x : HF A) :
    closure (lift e x) = (closure x).image (lift e) := by
  ext y
  have hh := congrArg (fun z : Finset (HF B) => y ∈ z) (Operational.lift_closure e x)
  simpa only [mem_image] using Iff.of_eq hh

omit [Fintype A] [Fintype B] in
lemma lift_TC (e : A ≃ B) (x : HF A) : TC (lift e x) = (TC x).image (lift e) := by
  simp only [TC,lift_elements,biUnion_image,image_biUnion,lift_closureHF]

omit [Fintype A] [Fintype B] in
lemma lift_TC_card (e : A ≃ B) (x : HF A) : (TC (lift e x)).card = (TC x).card := by
  rw [lift_TC,card_image_of_injective _ (lift e).injective]

omit [Fintype A] [Fintype B] in
lemma lift_cons (e : A ≃ B) {n : ℕ} (env : Fin n → HF A) (x : HF A) :
    (fun j => lift e ((Fin.cons x env : Fin (n+1) → HF A) j)) =
      Fin.cons (lift e x) (fun j => lift e (env j)) := by
  funext j; exact Fin.cases rfl (fun _ => rfl) j

omit [Fintype A] [Fintype B] in
lemma tracedLoop_transport (e : A ≃ B) (p : ℕ)
    (a : HF A → Traced A (HF A)) (b : HF B → Traced B (HF B))
    (h : ∀ x, b (lift e x) = (lift e (a x).1,(a x).2.image (lift e)))
    (fuel : ℕ) (x : HF A) :
    tracedLoop p b fuel (lift e x) =
      (lift e (tracedLoop p a fuel x).1,(tracedLoop p a fuel x).2.image (lift e)) := by
  induction fuel generalizing x with
  | zero => simp only [tracedLoop,lift_emptyHF,closure_emptyHF,image_singleton]
  | succ fuel ih =>
    simp only [tracedLoop,lift_TC_card,h,Equiv.apply_eq_iff_eq]
    split_ifs with hb he
    · rfl
    · simp only [ih,image_union]
    · simp only [lift_emptyHF,closure_emptyHF,image_singleton]

omit [Fintype A] [Fintype B] in
lemma selected_transport (e : A ≃ B) (r : HF A)
    (a : HF A → Bool) (b : HF B → Bool) (h : ∀ x, b (lift e x) = a x) :
    ((elements (lift e r)).filter (fun y => b y = true)) =
      ((elements r).filter (fun x => a x = true)).image (lift e) := by
  rw [lift_elements]
  ext y
  simp only [mem_filter,mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hy⟩
    exact ⟨x,⟨hx,by rwa [h] at hy⟩,rfl⟩
  · rintro ⟨x,⟨hx,hy⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,by rwa [h]⟩

mutual
  theorem Term.traced_transport (e : A ≃ B) (S : Input A) (T : Input B)
      (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (p : ℕ)
      {n : ℕ} (t : Term n) (env : Fin n → HF A) :
      t.traced T p (fun j => lift e (env j)) =
        (lift e (t.traced S p env).1,(t.traced S p env).2.image (lift e)) := by
    cases t with
    | var j => exact Prod.ext rfl (lift_closureHF e _)
    | empty => simp only [Term.traced,lift_emptyHF,closure_emptyHF,image_singleton]
    | atoms => simp only [Term.traced,← lift_atomsHF e,lift_closureHF]
    | pair a b =>
      simp only [Term.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        image_insert,image_union,lift_double]
    | union a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_insert,lift_unionHF]
    | unique a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_insert,lift_uniqueHF]
    | card a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_union,← lift_cardHF,lift_closureHF]
    | comprehend body range guard =>
      have hr := range.traced_transport e S T h p env
      have hg (x : HF A) := guard.traced_transport e S T h p (Fin.cons x env)
      have hb (x : HF A) := body.traced_transport e S T h p (Fin.cons x env)
      simp only [lift_cons] at hg hb
      have hs := selected_transport e (range.traced S p env).1
        (fun x => (guard.traced S p (Fin.cons x env)).1)
        (fun x => (guard.traced T p (Fin.cons x (fun j => lift e (env j)))).1)
        (fun x => congrArg Prod.fst (hg x))
      simp only [Term.traced,hr]
      rw [hs]
      simp only [image_image,Function.comp_def,hb,lift_ofFinset,
        lift_elements,biUnion_image,image_insert,image_union,image_biUnion,hg]
      congr 2 <;> first | rfl | (apply congrArg ofFinset; ext z; simp only [mem_image]) | (ext z; simp only [mem_image])
    | iterate step =>
      have hh (x : HF A) := step.traced_transport e S T h p (Fin.cons x env)
      simp only [lift_cons] at hh
      have hx := tracedLoop_transport e p
        (fun x => step.traced S p (Fin.cons x env))
        (fun x => step.traced T p (Fin.cons x (fun j => lift e (env j)))) hh (p+1) emptyHF
      simpa only [Term.traced,lift_emptyHF] using hx
  theorem Formula.traced_transport (e : A ≃ B) (S : Input A) (T : Input B)
      (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (p : ℕ)
      {n : ℕ} (f : Formula n) (env : Fin n → HF A) :
      f.traced T p (fun j => lift e (env j)) =
        ((f.traced S p env).1,(f.traced S p env).2.image (lift e)) := by
    cases f with
    | equal a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        Equiv.apply_eq_iff_eq,image_union]
    | input r a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        lift_inputHF e S T h,image_union]
    | neg a => simp only [Formula.traced,a.traced_transport e S T h p env]
    | and a b | or a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,image_union]
    | wsc step choice witness output => simp only [Formula.traced,image_empty]
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation

lemma realPolynomial_majorant (p : Polynomial ℝ) :
    ∃ q : Polynomial ℕ, ∀ n : ℕ, p.eval (n : ℝ) ≤ ((q.eval n : ℕ) : ℝ) := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨q,hq⟩ := ha
    obtain ⟨r,hr⟩ := hb
    refine ⟨q+r,fun n => ?_⟩
    simpa only [Polynomial.eval_add,Nat.cast_add] using add_le_add (hq n) (hr n)
  | monomial k a =>
    refine ⟨Polynomial.monomial k ⌈|a|⌉₊,fun n => ?_⟩
    simp only [Polynomial.eval_monomial,Nat.cast_mul,Nat.cast_pow]
    apply mul_le_mul_of_nonneg_right ((le_abs_self a).trans (Nat.le_ceil _))
    positivity

lemma resource_majorant (p : Polynomial ℝ) :
    ∃ q : Polynomial ℕ, ∀ n : ℕ, resource p n ≤ q.eval n := by
  obtain ⟨q,hq⟩ := realPolynomial_majorant p
  refine ⟨q,fun n => ?_⟩
  have hh := Nat.floor_mono (hq n)
  simpa only [resource,Nat.floor_natCast] using hh

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

open WitnessedSeparation.Grid WitnessedSeparation.Counting Finset

open WitnessedSeparation.Operational (lift)

variable {n : ℕ}

lemma Formula.grid_trace_invariant (f : Formula 0) (b : Vertex n → Grid.Scalar)
    (p : ℕ) : ∀ g : BoxGroup n, ∀ x ∈ (f.traced (atomInput b) p Fin.elim0).2,
      g • x ∈ (f.traced (atomInput b) p Fin.elim0).2 := by
  intro g x hx
  have ht := f.traced_transport (actionIso (b := b) g).toEquiv (atomInput b) (atomInput b)
    (fun r a c => (actionIso g).rel_eq r a c) p Fin.elim0
  have he : (fun j : Fin 0 => lift (actionIso (b := b) g).toEquiv (Fin.elim0 j)) = Fin.elim0 :=
    funext (fun j => Fin.elim0 j)
  rw [he] at ht
  have hm : g • x ∈ (f.traced (atomInput b) p Fin.elim0).2.image
      (lift (actionIso (b := b) g).toEquiv) := mem_image.mpr ⟨x,hx,rfl⟩
  exact (congrArg (fun z => g • x ∈ z.2) ht).mpr hm

lemma Formula.grid_trace_supported (f : Formula 0) (b : Vertex n → Grid.Scalar)
    (hn : 1 ≤ n) (p K N q : ℕ) (hN : 0 < N)
    (hb : (f.traced (atomInput b) p Fin.elim0).2.card ≤ K) (hK : K ≤ N^q) :
    ∀ x ∈ (f.traced (atomInput b) p Fin.elim0).2,
      HereditarilySupported (G := CentralGroup n)
        ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ x := by
  apply invariant_family_hereditarily_supported hn _ (f.grid_trace_invariant b p)
    (fun x hx y hy => f.traced_closed (atomInput b) p Fin.elim0 x hx
      (closure_member_subset hy (mem_closure_self y))) N hN (q:ℝ) (by positivity)
  rw [Real.rpow_natCast]
  exact_mod_cast hb.trans hK

lemma Formula.grid_traced_agrees (f : Formula 0) (hf : f.wscCount = 0)
    {m M N : ℕ} (vstar : Vertex n) (hn : 1 ≤ n) (p K q : ℕ)
    (hN : 0 < N) (hK : K ≤ N^q)
    (hb : ∀ i : Bool, (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2.card ≤ K)
    (hm : f.graphWidth ≤ m) (hmpos : 0 < m)
    (hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (f.traced (atomInput (twoCharges vstar false)) p Fin.elim0).1 =
      (f.traced (atomInput (twoCharges vstar true)) p Fin.elim0).1 := by
  let s := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have ht (i : Bool) : AdmissibleTrace (D i) K
      (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2 := by
    intro x hx
    refine ⟨f.grid_trace_supported (twoCharges vstar i) hn p K N q hN (hb i) hK x hx,?_⟩
    exact (card_le_card ((elements_subset_closure x).trans
      (f.traced_closed (atomInput (twoCharges vstar i)) p Fin.elim0 x hx))).trans (hb i)
  have hu := f.uniform_graph D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => atomInput (twoCharges vstar i)) (op_input_uniform (twoCharges vstar)) p K true hm
  have he : UniformDefinable C m 0 (fun i _ =>
      (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).1 = true) := by
    apply hu.congr
    intro i env
    have he : (fun j : Fin 0 => (env j).val) = Fin.elim0 := funext (fun j => Fin.elim0 j)
    constructor
    · intro hg
      have hh := f.graph_sound (D i) (atomInput (twoCharges vstar i)) p K
        (program_domain_transitive (twoCharges vstar) i) true env hg
      simpa only [he] using hh.symm
    · intro hg
      apply f.graph_complete (D i) (atomInput (twoCharges vstar i)) p K
        (program_domain_transitive (twoCharges vstar) i)
        (program_pure (twoCharges vstar) hn i 0) hf true env
      · simpa only [he] using ht i
      · simpa only [he] using hg.symm
  obtain ⟨φ,hφ,hφsem⟩ := he (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Grid.Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  apply Bool.eq_iff_iff.mpr
  exact (hφsem false v).symm.trans ((grid_hf_transfer hn hs hmpos vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open WitnessedSeparation.Grid WitnessedSeparation.Quantitative

def gridInput {n : ℕ} (b : Vertex n → Grid.Scalar) : FiniteInput :=
  ⟨Atom b,inferInstance,atomInput b⟩

theorem Sentence.agrees_on_some_grid_pair (ψ : Sentence) (hψ : ψ.isCPT) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ vstar : Vertex n,
      ψ.eval (gridInput (0 : Vertex n → Grid.Scalar)) =
        ψ.eval (gridInput (Pi.single vstar 1)) := by
  obtain ⟨r,hr⟩ := resource_majorant ψ.polynomial
  let Q : Polynomial ℕ := ψ.formula.traceBound.comp (Polynomial.X+r+1)
  obtain ⟨c,d,hcd⟩ := PolynomialCost.eval_bound Q
  let q := timeExponent c d
  let m := ψ.formula.graphWidth+1
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q (by
    have h := timeExponent_ge_two c d; omega) m
  refine ⟨n,hn,fun vstar => ?_⟩
  let N := atomSizeConstant*(n+1)^3
  let p := resource ψ.polynomial (Fintype.card (Atom (0 : Vertex n → Grid.Scalar)))
  let K := N^q
  have hN : 2 ≤ N := hnum.1
  have hc : Fintype.card (Atom (0 : Vertex n → Grid.Scalar)) =
      Fintype.card (Atom (Pi.single vstar 1)) := atom_card_independent hn _ _
  have hinput (i : Bool) : Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    (atom_card_bounds hn _).2
  have hres (i : Bool) : resource ψ.polynomial
      (Fintype.card (Atom (twoCharges vstar i))) = p := by
    cases i
    · rfl
    · exact congrArg (resource ψ.polynomial) hc.symm
  have hp : p ≤ r.eval N := (hr _).trans (PolynomialCost.eval_mono r (hinput false))
  have hb (i : Bool) : (ψ.formula.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2.card ≤ K := by
    calc
      _ ≤ ψ.formula.traceBound.eval (N+r.eval N+1) :=
        ψ.formula.traced_card_le _ p Fin.elim0 _ (by
          simp only [tracePotential,Fin.sum_univ_zero,Nat.add_zero]
          have hi := hinput i
          omega)
      _ = Q.eval N := by simp only [Q,Polynomial.eval_comp,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      _ ≤ c*(N+1)^d := hcd N
      _ ≤ K := (polynomial_bounds c d N hN).2.2.1
  have hh := ψ.formula.grid_traced_agrees hψ (m := m) vstar hn p K q
    (by omega : 0 < N) (le_refl K) hb (by omega) (by omega)
    hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  dsimp only [Sentence.eval,gridInput]
  rw [ψ.formula.eval_traced _ _ hψ,ψ.formula.eval_traced _ _ hψ]
  change some (ψ.formula.traced (atomInput (0 : Vertex n → Grid.Scalar)) p Fin.elim0).1 = _
  rw [← hc]
  exact congrArg some hh

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

def fullAut (S : Input A) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ r a b, S.rel r (g a) (g b) = S.rel r a b}
  one_mem' := by intro r a b; rfl
  mul_mem' := by
    intro g h hg hh r a b
    exact (hg r (h a) (h b)).trans (hh r a b)
  inv_mem' := by
    intro g hg r a b
    symm
    simpa using hg r (g⁻¹ a) (g⁻¹ b)

def paramAut (S : Input A) (α : HF A) : Subgroup (Equiv.Perm A) :=
  fullAut S ⊓ MulAction.stabilizer (Equiv.Perm A) α

def stateCode (x : Finset A) : HF A := ofFinset (x.image atom)

def choiceCode : Option A → HF A
  | none => ordinal 0
  | some a => atom a

structure Selection (A : Type) where
  candidates : Finset A → Finset A
  witnesses : Finset A → Finset (Equiv.Perm A)

namespace Selection

variable (P : Selection A)

def TransitiveAt (x : Finset A) : Prop :=
  ∀ a ∈ P.candidates x, ∀ b ∈ P.candidates x,
    ∃ g ∈ P.witnesses x, g a = b

def choices (x : Finset A) : Finset (Option A) :=
  if (P.candidates x).Nonempty ∧ P.TransitiveAt x then
    (P.candidates x).image some
  else {none}

def advance (x : Finset A) : Option A → Finset A
  | none => x
  | some a => insert a x

def Prefix (b : ℕ → Finset A) (c : ℕ → Option A) (k : ℕ) : Prop :=
  b 0 = ∅ ∧ ∀ i < k, c i ∈ P.choices (b i) ∧ b (i+1) = advance (b i) (c i)

def FirstStabilization (b : ℕ → Finset A) (c : ℕ → Option A) (t : ℕ) : Prop :=
  P.Prefix b c (t+1) ∧ (∀ i < t, b i ≠ b (i+1)) ∧ b t = b (t+1)

def witnessAt (_terminal intermediate : Finset A) : Finset (Equiv.Perm A) :=
  P.witnesses intermediate

def HistoryAut (S : Input A) (α : HF A) (b : ℕ → Finset A) (i : ℕ)
    (g : Equiv.Perm A) : Prop :=
  g ∈ paramAut S α ∧ ∀ j ≤ i, g • stateCode (b j) = stateCode (b j)

def WitnessedAt (S : Input A) (α : HF A) (b : ℕ → Finset A)
    (terminal : Finset A) (i : ℕ) : Prop :=
  (P.choices (b i)).Nonempty ∧
  (∀ g ∈ P.witnessAt terminal (b i), HistoryAut S α b i g) ∧
  ∀ u ∈ P.choices (b i), ∀ v ∈ P.choices (b i),
    ∃ g ∈ P.witnessAt terminal (b i), g • choiceCode u = choiceCode v

def Filtered (S : Input A) (α : HF A) : Prop :=
  (∀ x, (1 : Equiv.Perm A) ∈ P.witnesses x) ∧
  (∀ x g, g ∈ P.witnesses x → g ∈ paramAut S α) ∧
  (∀ x g, g ∈ P.witnesses x → ∀ a ∈ x, g a = a)

def Fresh : Prop := ∀ x a, a ∈ P.candidates x → a ∉ x

def Equivariant (S : Input A) (α : HF A) : Prop :=
  ∀ g ∈ paramAut S α, ∀ x,
    P.candidates (x.image g) = (P.candidates x).image g ∧
    P.witnesses (x.image g) = (P.witnesses x).image (fun h => g * h * g⁻¹)

end Selection

end

end WitnessedChoice

end

end OAI
