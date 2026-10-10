import Mathlib

namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

inductive Program (K : Type) where
  | skip
  | push (k : K) (b : Bool)
  | seq (p q : Program K)
  | cases (k : K) (nil ff tt : Program K)
  | loop (k : K) (ff tt : Program K)

def Node {K : Type} : Program K → Type
  | .skip | .push _ _ => Unit
  | .seq p q => Node p ⊕ Node q
  | .cases _ a b c => Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))
  | .loop _ b c => Unit ⊕ (Node b ⊕ Node c)

noncomputable instance nodeFintype {K : Type} (p : Program K) : Fintype (Node p) := by
  induction p with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push => exact inferInstanceAs (Fintype Unit)
  | seq p q hp hq => letI := hp; letI := hq; exact inferInstanceAs (Fintype (Node p ⊕ Node q))
  | cases k a b c ha hb hc =>
    letI := ha; letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))))
  | loop k b c hb hc =>
    letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node b ⊕ Node c)))

def entry {K : Type} : (p : Program K) → Node p
  | .skip | .push _ _ => ()
  | .seq p _ => .inl (entry p)
  | .cases _ _ _ _ | .loop _ _ _ => .inl ()

abbrev Store (K : Type) := K → List Bool
abbrev Config (K Λ : Type) := Cfg (fun _ : K => Bool) Λ (Option Bool)
def configured {K Λ : Type} (l : Λ) (s : Store K) : Config K Λ := ⟨some l,none,s⟩
def jump {K Λ : Type} (l : Λ) : Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))
def dispatch {K Λ : Type} (k : K) (nil ff tt : Λ) :
    Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .pop k (fun _ b => b) (.branch Option.isSome
    (.branch (fun b => b.getD false) (jump tt) (jump ff)) (jump nil))

def statement {K Λ : Type} : (p : Program K) → Λ → (Node p → Λ) → Node p →
    Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .skip,e,_,_ => jump e
  | .push k b,e,_,_ => .push k (fun _ => b) (jump e)
  | .seq p q,_e,w,.inl i => statement p (w (.inr (entry q))) (w ∘ Sum.inl) i
  | .seq _ q,e,w,.inr i => statement q e (w ∘ Sum.inr) i
  | .cases k a b c,_,w,.inl _ => dispatch k
      (w (.inr (.inl (entry a)))) (w (.inr (.inr (.inl (entry b)))))
      (w (.inr (.inr (.inr (entry c)))))
  | .cases _ a _ _,e,w,.inr (.inl i) => statement a e (w ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ b _,e,w,.inr (.inr (.inl i)) =>
      statement b e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ _ c,e,w,.inr (.inr (.inr i)) =>
      statement c e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) i
  | .loop k b c,e,w,.inl _ => dispatch k e
      (w (.inr (.inl (entry b)))) (w (.inr (.inr (entry c))))
  | .loop _ b _,_,w,.inr (.inl i) =>
      statement b (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl) i
  | .loop _ _ c,_,w,.inr (.inr i) =>
      statement c (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr) i

inductive Runs {K : Type} [DecidableEq K] : Program K → Store K → Store K → ℕ → Prop
  | skip (s) : Runs .skip s s 1
  | push (s) (k) (b) : Runs (.push k b) s (Function.update s k (b :: s k)) 1
  | seq {p q s t u a b} : Runs p s t a → Runs q t u b → Runs (.seq p q) s u (b+a)
  | cases_nil {k p q r s t a} : s k=[] → Runs p s t a → Runs (.cases k p q r) s t (a+1)
  | cases_false {k p q r s t xs a} : s k=false::xs →
      Runs q (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | cases_true {k p q r s t xs a} : s k=true::xs →
      Runs r (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | loop_nil {k p q s} : s k=[] → Runs (.loop k p q) s s 1
  | loop_false {k p q s t u xs a b} : s k=false::xs →
      Runs p (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)
  | loop_true {k p q s t u xs a b} : s k=true::xs →
      Runs q (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)

lemma iterate_step {α : Type*} (f : α → Option α) (a b : α) (h : f a=some b) :
    (flip bind f)^[1] (some a) = some b := h
lemma iterate_comp {α : Type*} (f : α → Option α) (a b c : α) (k l : ℕ)
    (h : (flip bind f)^[k] (some a)=some b)
    (g : (flip bind f)^[l] (some b)=some c) :
    (flip bind f)^[l+k] (some a)=some c := by
  rw [Function.iterate_add_apply,h,g]

lemma dispatch_nil {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (hs : s k=[]) : stepAux (dispatch k a b c) none s = configured a s := by
  simp only [dispatch,stepAux,hs,List.head?_nil,List.tail_nil,Option.isSome_none,
    Bool.cond_false,jump]
  rw [← hs,Function.update_eq_self]
  rfl
lemma dispatch_false {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=false::xs) :
    stepAux (dispatch k a b c) none s = configured b (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,Bool.cond_false,jump]
  rfl
lemma dispatch_true {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=true::xs) :
    stepAux (dispatch k a b c) none s = configured c (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,jump]
  rfl

theorem compile_runs {K : Type} [DecidableEq K] {p : Program K}
    {s t : Store K} {c : ℕ} (h : Runs p s t c) :
    ∀ {Λ : Type} (e : Λ) (w : Node p → Λ)
      (M : Λ → Stmt (fun _ : K => Bool) Λ (Option Bool)),
      (∀ i, M (w i) = statement p e w i) →
      (flip bind (step M))^[c] (some (configured (w (entry p)) s)) = some (configured e t) := by
  induction h with
  | skip s =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | push s k b =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | @seq p q s t u a b hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (entry q))) t) _ a b
    · exact ihp _ _ M (fun i => hM (.inl i))
    · exact ihq _ _ M (fun i => hM (.inr i))
  | @cases_nil k p q r s t a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p)))) s) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inl i)))
  | @cases_false k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inl (entry q)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inl i))))
  | @cases_true k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inr (entry r)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inr i))))
  | @loop_nil k p q s hs =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w (.inl ()))) none s) = _
    rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
  | @loop_false k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inl i)))
      · exact ihq _ _ M hM
  | @loop_true k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (entry q))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inr i)))
      · exact ihq _ _ M hM

noncomputable def machine {K : Type} [Fintype K] [DecidableEq K] (input output : K) (p : Program K) :
    Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := Option (Node p)
  main := some (entry p)
  σ := Option Bool
  initialState := none
  m
    | none => .halt
    | some i => statement p none some i

lemma machine_alphabets_finite {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) : ∀ k, Finite ((machine input output p).Γ k) :=
  fun _ => (inferInstance : Finite Bool)

def singletonStore {K : Type} [DecidableEq K] (k : K) (v : List Bool) : Store K :=
  Function.update (fun _ => []) k v

noncomputable def machine_outputs {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) (s t : List Bool) (c : ℕ)
    (h : Runs p (singletonStore input s) (singletonStore output t) c) :
    Turing.TM2OutputsInTime (machine input output p) s (some t) (c+1) := by
  let tm := machine input output p
  have hi : Turing.initList tm s = configured (some (entry p)) (singletonStore input s) := by
    change Turing.initList (machine input output p) s = _
    unfold machine Turing.initList configured singletonStore
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; simp
    · simp [hk,Function.update]
  have hf : Turing.haltList tm t =
      (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := by
    change Turing.haltList (machine input output p) t = _
    unfold machine Turing.haltList singletonStore
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; simp
    · simp [hk,Function.update]
  have hr := compile_runs h (none : Option (Node p)) some tm.m (fun _ => rfl)
  refine ⟨⟨c+1,?_⟩,le_rfl⟩
  change (flip bind (step tm.m))^[c+1] (some (Turing.initList tm s)) =
    some (Turing.haltList tm t)
  rw [hi,hf]
  have hend : step tm.m (configured (none : Option (Node p)) (singletonStore output t)) =
      some (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := rfl
  rw [Nat.add_comm c 1]
  exact iterate_comp (step tm.m) _ _ _ c 1 hr (iterate_step _ _ _ hend)
end ExactQuantumFactoring.BitStackProgram

end



end OAI
