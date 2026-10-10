import OAI.Computability.TypeSystem.Interface

namespace OAI

namespace PureTypeSystem.SignedInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Vector := (T : Expr S) → SignedCandidate Ω T (hC.signing (Ω.profile T))

noncomputable def value (v : Vector Ω hC) (T : Expr S) : Set (Expr S) :=
  if Ω.profile T ∈ C then (v T).set else Top Ω T

theorem value_candidate (v : Vector Ω hC) (T : Expr S) :
    IsCandidate Ω T (value Ω hC v T) := by
  unfold value; split
  · exact (v T).candidate
  · exact top_candidate

theorem value_forward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = false) :
    value Ω hC v T ⊆ value Ω hC w T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,Bool.false_eq_true,ite_false] using hh
  · exact Set.Subset.rfl

theorem value_backward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = true) :
    value Ω hC w T ⊆ value Ω hC v T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,ite_true] using hh
  · exact Set.Subset.rfl

noncomputable def stepCandidate (v : Vector Ω hC) (T : Expr S) : Candidate Ω T :=
  match T with
  | .pi D E =>
    if Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C then
      ⟨ProductTest Ω D E (value Ω hC v D) (fun n => {value Ω hC v (E.instantiate n).normalForm}),
        productTest_candidate hw (value_candidate Ω hC v D).upper (by
          intro n _ X hX
          rcases Set.mem_singleton_iff.mp hX with rfl
          exact value_candidate Ω hC v _)⟩
    else ⟨Top Ω (.pi D E),top_candidate⟩
  | T => ⟨Top Ω T,top_candidate⟩

noncomputable def step (v : Vector Ω hC) : Vector Ω hC :=
  fun T => SignedCandidate.wrap (stepCandidate Ω hC hw v T)

include hno in
theorem step_monotone : Monotone (step Ω hC hw) := by
  intro v w hv T
  apply (SignedCandidate.order _ _).mpr
  simp only [step,SignedCandidate.set_wrap]
  cases T with
  | sort s => cases hC.signing (Ω.profile (.sort s)) <;> exact Set.Subset.rfl
  | var i => cases hC.signing (Ω.profile (.var i)) <;> exact Set.Subset.rfl
  | lam D E => cases hC.signing (Ω.profile (.lam D E)) <;> exact Set.Subset.rfl
  | app f n => cases hC.signing (Ω.profile (.app f n)) <;> exact Set.Subset.rfl
  | pi D E =>
    dsimp only [stepCandidate]
    by_cases H : Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C
    · simp only [ite_eq_left H]
      obtain ⟨hn,⟨s,ht⟩,hpC⟩ := H
      have hd : ∀ hD : Ω.profile D ∈ C,
          hC.signing (Ω.profile (.pi D E)) = Bool.xor (hC.signing (Ω.profile D)) true := by
        intro hD
        obtain ⟨a,b,c,hD',hE,hr,hconv⟩ := ht.choose_spec.generation_pi
        have hf := Profile.triple hw ht.choose_spec
        have hglob : ProfileTriple P (Ω.profile D)
            (Profile P (D.rename (Expr.reverseIndex ht.choose) :: Ω.context ht.choose)
              (E.rename (Expr.liftRen (Expr.reverseIndex ht.choose)))) (Ω.profile (.pi D E)) := by
          rw [Ω.profile_at hw hD',Ω.profile_at hw ht.choose_spec]
          exact hf
        exact hC.signing_cross hno hD hpC (.singleton (.domain hglob))
      have he : ∀ n, Ω.HasType n D → Ω.profile (E.instantiate n).normalForm ∈ C →
          hC.signing (Ω.profile (E.instantiate n).normalForm) = hC.signing (Ω.profile (.pi D E)) := by
        intro n hn hnc
        rw [Ω.profile_normalForm] at hnc ⊢
        simpa only [Bool.xor_false] using
          (hC.signing_cross hno hnc hpC (Ω.profile_instantiate_product_path hw ht hn).parity).symm
      have flip (a b : Bool) (h : a = Bool.xor b true) : b = !a := by
        cases a <;> cases b <;> cases h <;> rfl
      cases hs : hC.signing (Ω.profile (.pi D E)) with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC v D := value_backward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_forward Ω hC hv (fun hc => (he n (value_candidate Ω hC w D |>.upper hn).1 hc).trans hs) hout
      | true =>
        simp only [ite_true]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC w D := value_forward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_backward Ω hC hv (fun hc => (he n (value_candidate Ω hC v D |>.upper hn).1 hc).trans hs) hout
    · simp only [ite_eq_right H]
      cases hC.signing (Ω.profile (.pi D E)) <;> exact Set.Subset.rfl

noncomputable def operator : Vector Ω hC →o Vector Ω hC :=
  ⟨step Ω hC hw,step_monotone Ω hC hw hno⟩

noncomputable def fixed : Vector Ω hC := (operator Ω hC hw hno).lfp

noncomputable def actual (T : Expr S) : Set (Expr S) := value Ω hC (fixed Ω hC hw hno) T

theorem actual_candidate (T : Expr S) : IsCandidate Ω T (actual Ω hC hw hno T) :=
  value_candidate Ω hC _ T

theorem actual_outside {T : Expr S} (ho : Ω.profile T ∉ C) : actual Ω hC hw hno T = Top Ω T := by
  simp only [actual,value,ho,ite_false]

theorem actual_product {D E : Expr S} {s : S} (hn : Normal (.pi D E))
    (ht : Ω.HasType (.pi D E) (.sort s)) (hc : Ω.profile (.pi D E) ∈ C) :
    actual Ω hC hw hno (.pi D E) =
      ProductTest Ω D E (actual Ω hC hw hno D) (fun n => {actual Ω hC hw hno (E.instantiate n).normalForm}) := by
  have he := congrArg (fun v : Vector Ω hC => (v (.pi D E)).set) (operator Ω hC hw hno).map_lfp
  change (step Ω hC hw (fixed Ω hC hw hno) (.pi D E)).set = _ at he
  dsimp only [step,SignedCandidate.set_wrap,stepCandidate] at he
  rw [ite_eq_left (show Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧
    Ω.profile (.pi D E) ∈ C from ⟨hn,⟨s,ht⟩,hc⟩)] at he
  simpa only [actual,value,hc,ite_true,SignedCandidate.set_wrap,fixed] using he.symm
end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Environment (Γ : List (Expr S)) := {σ : Nat → Expr S // Ω.TypedSubstitution Γ σ}

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  if Profile P Γ A ∈ C then actual Ω hC hw hno (A.subst e.val).normalForm
  else Top Ω (A.subst e.val).normalForm

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.val).normalForm (R Ω hC hw hno A e) := by
  unfold R; split
  · exact actual_candidate Ω hC hw hno _
  · exact top_candidate

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ)
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.val) ∉ C) :
    R Ω hC hw hno A e = Top Ω (A.subst e.val).normalForm := by
  unfold R; split
  · exact actual_outside Ω hC hw hno (by
      rw [Ω.profile_normalForm]; exact ho.resolve_left (not_not.mpr ‹_›))
  · rfl

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (e : Environment Ω Γ) (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) :
    R Ω hC hw hno A e = R Ω hC hw hno B e := by
  have hwa : WeaklyNormalizing A := by
    rcases hA with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hwb : WeaklyNormalizing B := by
    rcases hB with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hp := Profile.converts (P := P) (Γ := Γ) hwa hwb hc
  have hn := Expr.normalForm_converts (hA.subst_wn hw e.property) (hB.subst_wn hw e.property) (hc.subst e.val)
  simp only [R,hp,hn]

theorem actual_sort (s : S) : actual Ω hC hw hno (.sort s) = Top Ω (.sort s) := by
  by_cases hc : Ω.profile (.sort s) ∈ C
  · have he := congrArg (fun v : Vector Ω hC => (v (.sort s)).set) (operator Ω hC hw hno).map_lfp
    change (step Ω hC hw (fixed Ω hC hw hno) (.sort s)).set = _ at he
    simpa only [step,stepCandidate,SignedCandidate.set_wrap,actual,value,hc,ite_true,fixed] using he.symm
  · exact actual_outside Ω hC hw hno hc

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω hC hw hno (.sort s) e = Top Ω (.sort s) := by
  simp only [R,Expr.subst,Expr.normalForm_of_normal (Normal.sort s),actual_sort,ite_self]

theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A)
    (he : f.val = Expr.extend e.val n) :
    R Ω hC hw hno (A.rename Nat.succ) f = R Ω hC hw hno A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω hC hw hno a f).trans (R_sort Ω hC hw hno a e).symm
  · simp only [R,Profile.weaken hw hA hD,he,Expr.subst_raise_extend]

theorem R_before {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment Ω Γ)
    (hp : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K) :
    R Ω hC hw hno A e = actual Ω hC hw hno (A.subst e.val).normalForm := by
  unfold R; split
  · rfl
  · rename_i hn
    refine (actual_outside Ω hC hw hno ?_).symm
    rw [Ω.profile_normalForm]
    intro ha
    obtain ⟨K,hK,hp⟩ := hp
    exact hn (hC.between ha hK (Ω.profile_subst_path hw hA e.property).reach hp)

/-- The actual fixed point tests precisely every raw argument; normalization of
its codomain commutes with this specialization by confluence. -/
theorem actual_raw_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (e : Environment Ω Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C) (h : Expr S) :
    h ∈ actual Ω hC hw hno ((Expr.pi D E).subst e.val).normalForm ↔
    h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm ∧
      ∀ n, n ∈ actual Ω hC hw hno (D.subst e.val).normalForm →
        Expr.app h n ∈ actual Ω hC hw hno (E.subst (Expr.extend e.val n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp e.property
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))) at hwraw
  have hparts : WeaklyNormalizing (D.subst e.val) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub e.val)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have hnf := Expr.normalForm_pi hparts.1 hparts.2
  have hpN := hraw.normalForm hw
  change Ω.HasType (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm (.sort s) at hpN
  rw [hnf] at hpN
  have hNC : Ω.profile (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) ∈ C := by
    rw [← hnf,Ω.profile_normalForm]; exact ha
  have hnormal : Normal (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) :=
    .pi (Expr.normalForm_spec hparts.1).2 (Expr.normalForm_spec hparts.2).2
  have hbody (n : Expr S) (hn : n ∈ actual Ω hC hw hno (D.subst e.val).normalForm) :
      (E.subst (Expr.extend e.val n)).normalForm =
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n).normalForm := by
    have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
    have hrawD := ContextTower.HasType.subst hD e.property
    have hnr := hnt.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    have htarget := ContextTower.HasType.subst hE (e.property.cons hnr)
    obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hnt
    have hr : Reduces (E.subst (Expr.extend e.val n))
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n) := by
      rw [← Expr.instantiate_extended]
      exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
    exact Expr.normalForm_converts (htarget.weaklyNormalizing hw) (ht.weaklyNormalizing hw) hr.converts
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔ _
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔
    h ∈ Top Ω (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ∧ _
  rw [hnf,actual_product Ω hC hw hno hnormal hpN hNC]
  constructor
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn
    rw [hbody n hn]
    exact hb n hn _ (Set.mem_singleton _)
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    rw [← hbody n hn]
    exact hb n hn

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (ht : h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm)
    (hb : ∀ n, n ∈ R Ω hC hw hno D e → ∀ f : Environment Ω (D :: Γ),
      f.val = Expr.extend e.val n → Expr.app h n ∈ R Ω hC hw hno E f) :
    h ∈ R Ω hC hw hno (.pi D E) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  simp only [R,hg,ite_true]
  apply (actual_raw_product Ω hC hw hno hp e ha h).mpr
  refine ⟨ht,?_⟩
  intro n hn
  have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
  have hrawD := ContextTower.HasType.subst hD e.property
  have hnr := hnt.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.val n,e.property.cons hnr⟩
  have he := R_before Ω hC hw hno hE f ⟨_,hg,.single (.codomain hf)⟩
  have hh := hb n (hd.symm ▸ hn) f rfl
  exact he ▸ hh

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s)) (hN : HasType P Γ N D)
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (hh : h ∈ R Ω hC hw hno (.pi D E) e)
    (hn : N.subst e.val ∈ R Ω hC hw hno D e) :
    Expr.app h (N.subst e.val) ∈ R Ω hC hw hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  have he := R_before Ω hC hw hno (hE.instantiate hN) e
    ⟨_,hg,(Profile.instantiate_product_path hw hp hN).reach⟩
  simp only [R,hg,ite_true] at hh
  have hout := (actual_raw_product Ω hC hw hno hp e ha h).mp hh |>.2 _ (hd ▸ hn)
  rw [he,← Expr.instantiate_subst,Expr.instantiate_extended]
  exact hout

noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Subtype.val
  typed := Subtype.property
  inhabit σ hσ := ⟨⟨σ,hσ⟩,rfl⟩
  Ext e f n := f.val = Expr.extend e.val n
  ext_images he := he
  extend e _ _ hn := ⟨⟨_,e.property.cons hn⟩,rfl⟩
  R := R Ω hC hw hno
  candidate e _ := R_candidate Ω hC hw hno _ e
  conversion e ha hb hc := R_conversion Ω hC hw hno e ha hb hc
  outside e _ ho := R_outside Ω hC hw hno _ e ho
  weakening hd he hx := R_weakening Ω hC hw hno hd he hx
  product_intro e hp hg ha h ht hb := product_intro Ω hC hw hno e hp hg ha h ht hb
  specialization e hp hn hg ha h hh hN := specialization Ω hC hw hno e hp hn hg ha h hh hN

end PureTypeSystem.SignedInterpretation

end OAI
