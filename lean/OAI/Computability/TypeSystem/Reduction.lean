import OAI.Computability.TypeSystem.Basic

namespace OAI

namespace PureTypeSystem

universe u

/-- Parallel reduction is used only to establish the beta metatheory. -/
inductive Parallel {S : Type u} : Expr S → Expr S → Prop
  | var (n) : Parallel (.var n) (.var n)
  | sort (s) : Parallel (.sort s) (.sort s)
  | app {f f' a a'} : Parallel f f' → Parallel a a' →
      Parallel (.app f a) (.app f' a')
  | lam {A A' b b'} : Parallel A A' → Parallel b b' →
      Parallel (.lam A b) (.lam A' b')
  | pi {A A' B B'} : Parallel A A' → Parallel B B' →
      Parallel (.pi A B) (.pi A' B')
  | head {b b' a a'} (A) : Parallel b b' → Parallel a a' →
      Parallel (.app (.lam A b) a) (b'.instantiate a')

namespace Parallel

variable {S : Type u} {M N : Expr S}

@[refl] theorem refl (M : Expr S) : Parallel M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem of_beta (h : Beta M N) : Parallel M N := by
  induction h with
  | head A b a => exact .head A (refl b) (refl a)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih

theorem rename (h : Parallel M N) (ρ : Nat → Nat) :
    Parallel (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ _ ihb iha =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Parallel.head (A.rename ρ) (ihb (Expr.liftRen ρ)) (iha ρ))

theorem subst (h : Parallel M N) (σ τ : Nat → Expr S)
    (hστ : ∀ n, Parallel (σ n) (τ n)) : Parallel (M.subst σ) (N.subst τ) := by
  have hlift (σ τ : Nat → Expr S) (hστ : ∀ n, Parallel (σ n) (τ n)) :
      ∀ n, Parallel (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hστ n).rename Nat.succ
  induction h generalizing σ τ with
  | var n => exact hστ n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app (ihf σ τ hστ) (iha σ τ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))
  | head A _ _ ihb iha =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Parallel.head (A.subst σ) (ihb _ _ (hlift σ τ hστ)) (iha σ τ hστ))

theorem instantiate {b b' a a' : Expr S} (hb : Parallel b b') (ha : Parallel a a') :
    Parallel (b.instantiate a) (b'.instantiate a') := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

end Parallel

namespace Expr

variable {S : Type u}

/-- Takahashi's complete development, including type annotations. -/
def develop : Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app (lam _ b) a => (develop b).instantiate (develop a)
  | app f a => app (develop f) (develop a)
  | lam A b => lam (develop A) (develop b)
  | pi A B => pi (develop A) (develop B)

end Expr

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem triangle (h : Parallel M N) : Parallel N M.develop := by
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | @app f f' a a' hf ha ihf iha =>
      cases f with
      | var n => exact .app ihf iha
      | sort s => exact .app ihf iha
      | app f b => exact .app ihf iha
      | pi A B => exact .app ihf iha
      | lam A b =>
          cases hf with
          | lam hA hb =>
              cases ihf with
              | lam ihA ihb => exact .head _ ihb iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | head A _ _ ihb iha => exact ihb.instantiate iha

theorem diamond {a b c : Expr S} (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d := ⟨a.develop, hab.triangle, hac.triangle⟩

end Parallel

abbrev Reduces {S : Type u} := Relation.ReflTransGen (@Beta S)

namespace Reduces

variable {S : Type u} {f f' a a' A A' b b' : Expr S}

theorem app (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app f a) (.app f' a') := by
  exact (hf.lift (fun x => Expr.app x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app f' x) (fun _ _ h => Beta.app_right h))

theorem lam (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.lam A b) (.lam A' b') := by
  exact (hA.lift (fun x => Expr.lam x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam A' x) (fun _ _ h => Beta.lam_body h))

theorem pi (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.pi A b) (.pi A' b') := by
  exact (hA.lift (fun x => Expr.pi x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi A' x) (fun _ _ h => Beta.pi_body h))

theorem rename {M N : Expr S} (h : Reduces M N) (ρ : Nat → Nat) :
    Reduces (M.rename ρ) (N.rename ρ) := h.lift _ (fun _ _ h => h.rename ρ)

theorem subst {M N : Expr S} (h : Reduces M N) (σ : Nat → Expr S) :
    Reduces (M.subst σ) (N.subst σ) := h.lift _ (fun _ _ h => h.subst σ)

end Reduces

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem reduces (h : Parallel M N) : Reduces M N := by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | app _ _ ihf iha => exact Reduces.app ihf iha
  | lam _ _ ihA ihb => exact Reduces.lam ihA ihb
  | pi _ _ ihA ihB => exact Reduces.pi ihA ihB
  | head A _ _ ihb iha =>
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _)

theorem rtc_reduces {M N : Expr S} (h : Relation.ReflTransGen Parallel M N) :
    Reduces M N := Relation.reflTransGen_closed (fun _ _ h => h.reduces) _ _ h

end Parallel

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem parallel (h : Reduces M N) : Relation.ReflTransGen Parallel M N :=
  Relation.ReflTransGen.mono (fun _ _ h => Parallel.of_beta h) _ _ h

theorem confluent {a b c : Expr S} (hab : Reduces a b) (hac : Reduces a c) :
    Relation.Join Reduces b c := by
  have hd : ∀ a b c : Expr S, Parallel a b → Parallel a c →
      ∃ d, Relation.ReflGen Parallel b d ∧ Relation.ReflTransGen Parallel c d := by
    intro a b c hab hac
    obtain ⟨d, hb, hc⟩ := Parallel.diamond hab hac
    exact ⟨d, .single hb, .single hc⟩
  obtain ⟨d, hb, hc⟩ := Relation.church_rosser hd hab.parallel hac.parallel
  exact ⟨d, Parallel.rtc_reduces hb, Parallel.rtc_reduces hc⟩

end Reduces

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem join (h : Converts M N) : Relation.Join Reduces M N := by
  induction h with
  | rel a b h => exact ⟨b, .single h, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
      obtain ⟨c, ha, hb⟩ := ih
      exact ⟨c, hb, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨d, ha, hb⟩ := ih₁
      obtain ⟨e, hb', hc⟩ := ih₂
      obtain ⟨f, hd, he⟩ := Reduces.confluent hb hb'
      exact ⟨f, ha.trans hd, hc.trans he⟩

end Converts

namespace Normal

variable {S : Type u} {M N : Expr S}

theorem reduces_eq (hM : Normal M) (h : Reduces M N) : M = N := by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))

theorem eq_of_converts (hM : Normal M) (hN : Normal N) (h : Converts M N) : M = N := by
  obtain ⟨K, hMK, hNK⟩ := h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm

end Normal

namespace Reduces

variable {S : Type u} {A B N : Expr S}

theorem pi_inv (h : Reduces (.pi A B) N) :
    ∃ A' B', N = .pi A' B' ∧ Reduces A A' ∧ Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ h ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases h with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail h, hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail h⟩

theorem converts {M N : Expr S} (h : Reduces M N) : Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h

end Reduces

namespace Converts

variable {S : Type u}

theorem product_compatibility {A B A' B' : Expr S}
    (h : Converts (.pi A B) (.pi A' B')) : Converts A A' ∧ Converts B B' := by
  obtain ⟨T, hT, hT'⟩ := h.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hT.pi_inv
  obtain ⟨D', E', hDE', hA', hB'⟩ := hT'.pi_inv
  have heq := Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨.trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩

end Converts

namespace Normal

variable {S : Type u}

theorem var (n : Nat) : Normal (.var n : Expr S) := by
  intro N h
  cases h

theorem sort (s : S) : Normal (.sort s) := by
  intro N h
  cases h

theorem stronglyNormalizing {M : Expr S} (h : Normal M) : StronglyNormalizing M :=
  .intro M (fun N hN => False.elim (h N hN))

end Normal

namespace StronglyNormalizing

variable {S : Type u} {M N : Expr S}

theorem step (hM : StronglyNormalizing M) (h : Beta M N) : StronglyNormalizing N :=
  hM.inv h

theorem reduces (hM : StronglyNormalizing M) (h : Reduces M N) : StronglyNormalizing N := by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact ih.step h

/-- SN of an image reflects along any map preserving individual reduction steps. -/
theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {M N}, Beta M N → Beta (f M) (f N)) {M : Expr S}
    (h : StronglyNormalizing (f M)) : StronglyNormalizing M := by
  have aux : ∀ N, StronglyNormalizing N → ∀ M, f M = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N _ ih =>
        intro M heq
        apply Acc.intro
        intro M' hM
        exact ih (f M') (heq ▸ hf hM) M' rfl
  exact aux _ h M rfl

theorem app_left {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing f := of_map (fun h => Beta.app_left h) h

theorem app_right {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing a := of_map (fun h => Beta.app_right h) h

theorem lam_domain {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing A := of_map (fun h => Beta.lam_domain h) h

theorem lam_body {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing b := of_map (fun h => Beta.lam_body h) h

theorem pi_domain {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing A := of_map (fun h => Beta.pi_domain h) h

theorem pi_body {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing B := of_map (fun h => Beta.pi_body h) h

theorem of_subst (σ : Nat → Expr S) (h : StronglyNormalizing (M.subst σ)) :
    StronglyNormalizing M := of_map (fun h => h.subst σ) h

theorem of_rename (ρ : Nat → Nat) (h : StronglyNormalizing (M.rename ρ)) :
    StronglyNormalizing M := of_map (fun h => h.rename ρ) h

theorem lam {A b : Expr S} (hA : StronglyNormalizing A) (hb : StronglyNormalizing b) :
    StronglyNormalizing (.lam A b) := by
  induction hA generalizing b with
  | intro A hA ihA =>
      induction hb with
      | intro b hb ihb =>
          apply Acc.intro
          intro N hN
          cases hN with
          | lam_domain h => exact ihA _ h (Acc.intro _ hb)
          | lam_body h => exact ihb _ h

theorem pi {A B : Expr S} (hA : StronglyNormalizing A) (hB : StronglyNormalizing B) :
    StronglyNormalizing (.pi A B) := by
  induction hA generalizing B with
  | intro A hA ihA =>
      induction hB with
      | intro B hB ihB =>
          apply Acc.intro
          intro N hN
          cases hN with
          | pi_domain h => exact ihA _ h (Acc.intro _ hB)
          | pi_body h => exact ihB _ h

end StronglyNormalizing

namespace Expr

variable {S : Type u}

def apps (f : Expr S) : List (Expr S) → Expr S
  | [] => f
  | a :: as => apps (.app f a) as

@[simp] theorem apps_nil (f : Expr S) : apps f [] = f := rfl
@[simp] theorem apps_cons (f a : Expr S) (as : List (Expr S)) :
    apps f (a :: as) = apps (.app f a) as := rfl

theorem apps_append (f : Expr S) (as bs : List (Expr S)) :
    apps f (as ++ bs) = apps (apps f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

end Expr

/-- Exactly one reduction step in one term of an argument list. -/
inductive ArgsStep {S : Type u} : List (Expr S) → List (Expr S) → Prop
  | head {a a' as} : Beta a a' → ArgsStep (a :: as) (a' :: as)
  | tail {a as as'} : ArgsStep as as' → ArgsStep (a :: as) (a :: as')

def StronglyNormalizingArgs {S : Type u} (as : List (Expr S)) : Prop :=
  Acc (fun bs as => ArgsStep as bs) as

namespace Beta

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Beta f f') (as : List (Expr S)) :
    Beta (f.apps as) (f'.apps as) := by
  induction as generalizing f f' with
  | nil => exact h
  | cons a as ih => exact ih (.app_left h)

/-- If the head is not a lambda, a spine step comes from its head or an argument. -/
theorem apps_inv {as : List (Expr S)} {N : Expr S}
    (hf : ∀ A b, f ≠ .lam A b) (h : Beta (f.apps as) N) :
    (∃ f', Beta f f' ∧ N = f'.apps as) ∨
    (∃ as', ArgsStep as as' ∧ N = f.apps as') := by
  induction as generalizing f N with
  | nil => exact .inl ⟨N, h, rfl⟩
  | cons a as ih =>
      obtain ⟨g, hg, rfl⟩ | ⟨as', has, rfl⟩ :=
        ih (f := .app f a) (by intro A b heq; cases heq) h
      · cases hg with
        | head A b a => exact False.elim (hf A b rfl)
        | app_left hg => exact .inl ⟨_, hg, rfl⟩
        | app_right hg => exact .inr ⟨_, .head hg, rfl⟩
      · exact .inr ⟨_, .tail has, rfl⟩

end Beta

namespace ArgsStep

variable {S : Type u} {as bs : List (Expr S)}

theorem apps (h : ArgsStep as bs) (f : Expr S) : Beta (f.apps as) (f.apps bs) := by
  induction h generalizing f with
  | head h => exact (Beta.app_right h).apps _
  | tail h ih => exact ih (.app f _)

end ArgsStep

namespace Reduces

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Reduces f f') (as : List (Expr S)) :
    Reduces (f.apps as) (f'.apps as) := h.lift _ (fun _ _ h => h.apps as)

end Reduces

namespace StronglyNormalizingArgs

variable {S : Type u}

theorem nil : StronglyNormalizingArgs ([] : List (Expr S)) := by
  apply Acc.intro
  intro bs h
  cases h

theorem cons {a : Expr S} {as : List (Expr S)} (ha : StronglyNormalizing a)
    (has : StronglyNormalizingArgs as) : StronglyNormalizingArgs (a :: as) := by
  induction ha generalizing as with
  | intro a ha iha =>
      induction has with
      | intro as has ihas =>
          apply Acc.intro
          intro bs h
          cases h with
          | head h => exact iha _ h (Acc.intro _ has)
          | tail h => exact ihas _ h

theorem of_forall {as : List (Expr S)} (h : ∀ a ∈ as, StronglyNormalizing a) :
    StronglyNormalizingArgs as := by
  induction as with
  | nil => exact nil
  | cons a as ih =>
      exact cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem head {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizing a :=
  Subrelation.accessible (fun h => ArgsStep.head h)
    (InvImage.accessible (fun a => a :: as) h)

theorem tail {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizingArgs as :=
  Subrelation.accessible (fun h => ArgsStep.tail h)
    (InvImage.accessible (fun as => a :: as) h)

theorem of_mem {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs as) (ha : a ∈ as) : StronglyNormalizing a := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.head
      · exact ih h.tail ha

end StronglyNormalizingArgs

namespace StronglyNormalizing

variable {S : Type u}

theorem apps_head {f : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizing (f.apps as)) : StronglyNormalizing f :=
  of_map (fun h => h.apps as) h

theorem var_apps (n : Nat) {as : List (Expr S)} (has : StronglyNormalizingArgs as) :
    StronglyNormalizing ((Expr.var n : Expr S).apps as) := by
  induction has with
  | intro as has ih =>
      apply Acc.intro
      intro N hN
      obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
        hN.apps_inv (by intro A b heq; cases heq)
      · cases hf
      · exact ih _ hbs

/-- The source's head-expansion lemma, with any finite argument spine.
The proof uses nested accessibility induction, not a raised recursion budget
or an assumed maximal reduction height. -/
theorem head_expansion {A b a : Expr S} {as : List (Expr S)}
    (hA : StronglyNormalizing A) (hb : StronglyNormalizing b)
    (ha : StronglyNormalizing a) (has : StronglyNormalizingArgs as)
    (hc : StronglyNormalizing ((b.instantiate a).apps as)) :
    StronglyNormalizing ((Expr.app (.lam A b) a).apps as) := by
  induction hA generalizing b a as with
  | intro A hA ihA =>
      induction hb generalizing a as with
      | intro b hb ihb =>
          induction ha generalizing as with
          | intro a ha iha =>
              induction has with
              | intro as has ihas =>
                  apply Acc.intro
                  intro N hN
                  obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
                    hN.apps_inv (by intro D c heq; cases heq)
                  · cases hf with
                    | head => exact hc
                    | app_left hf =>
                        cases hf with
                        | lam_domain h =>
                            exact ihA _ h (Acc.intro _ hb) (Acc.intro _ ha)
                              (Acc.intro _ has) hc
                        | lam_body h =>
                            exact ihb _ h (Acc.intro _ ha) (Acc.intro _ has)
                              (hc.step ((h.subst (Expr.single a)).apps as))
                    | app_right h =>
                        exact iha _ h (Acc.intro _ has)
                          (hc.reduces ((Parallel.instantiate (Parallel.refl b)
                            (Parallel.of_beta h)).reduces.apps as))
                  · exact ihas _ hbs (hc.step (hbs.apps _))

end StronglyNormalizing

namespace Expr
variable {S : Type u}
/-- Only literal syntax descent, including both annotations. -/
inductive Child : Expr S → Expr S → Prop
  | app_left (f a) : Child f (.app f a)
  | app_right (f a) : Child a (.app f a)
  | lam_domain (D m) : Child D (.lam D m)
  | lam_body (D m) : Child m (.lam D m)
  | pi_domain (D E) : Child D (.pi D E)
  | pi_body (D E) : Child E (.pi D E)

inductive Subterm : Expr S → Expr S → Prop
  | refl (M) : Subterm M M
  | tail {M N L} : Subterm M N → Child N L → Subterm M L

namespace Child
variable {M N M' : Expr S}
theorem beta_lift (h : Child M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Child M' N' := by
  cases h with
  | app_left f a => exact ⟨_,.app_left hr,.app_left _ _⟩
  | app_right f a => exact ⟨_,.app_right hr,.app_right _ _⟩
  | lam_domain D m => exact ⟨_,.lam_domain hr,.lam_domain _ _⟩
  | lam_body D m => exact ⟨_,.lam_body hr,.lam_body _ _⟩
  | pi_domain D E => exact ⟨_,.pi_domain hr,.pi_domain _ _⟩
  | pi_body D E => exact ⟨_,.pi_body hr,.pi_body _ _⟩

theorem sn (h : Child M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  cases h with
  | app_left => exact hs.app_left
  | app_right => exact hs.app_right
  | lam_domain => exact hs.lam_domain
  | lam_body => exact hs.lam_body
  | pi_domain => exact hs.pi_domain
  | pi_body => exact hs.pi_body
end Child

namespace Subterm
variable {M N L M' : Expr S}
theorem trans (h : Subterm M N) (h' : Subterm N L) : Subterm M L := by
  induction h' with
  | refl => exact h
  | tail _ hc ih => exact .tail ih hc

theorem of_child (h : Child M N) : Subterm M N := .tail (.refl M) h

theorem beta_lift (h : Subterm M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Subterm M' N' := by
  induction h with
  | refl => exact ⟨_,hr,.refl _⟩
  | tail h hc ih =>
    obtain ⟨N',hr',hs'⟩ := ih
    obtain ⟨L',hr'',hc'⟩ := hc.beta_lift hr'
    exact ⟨L',hr'',.tail hs' hc'⟩

theorem sn (h : Subterm M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  induction h with
  | refl => exact hs
  | tail h hc ih => exact ih (hc.sn hs)
end Subterm
end Expr

namespace StronglyNormalizing
variable {S : Type u}
/-- The manuscript's simultaneous reduction-height/syntax-size induction,
proved directly from accessibility, without choosing a height or raising limits. -/
theorem induction_subterms {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, Expr.Child N M → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have aux : ∀ M : Expr S, StronglyNormalizing M → ∀ N, Expr.Subterm N M → Q N := by
    intro M hs
    induction hs with
    | intro M hred ih =>
      intro N
      have hreds (N : Expr S) (hNM : Expr.Subterm N M) : ∀ L, Beta N L → Q L := by
        intro L hr
        obtain ⟨M',hr',hLM'⟩ := hNM.beta_lift hr
        exact ih M' hr' L hLM'
      induction N with
      | var n =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | sort s =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | app f a ihf iha =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | app_left => exact ihf ((Expr.Subterm.of_child (.app_left f a)).trans hn)
        | app_right => exact iha ((Expr.Subterm.of_child (.app_right f a)).trans hn)
      | lam D m ihD ihm =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | lam_domain => exact ihD ((Expr.Subterm.of_child (.lam_domain D m)).trans hn)
        | lam_body => exact ihm ((Expr.Subterm.of_child (.lam_body D m)).trans hn)
      | pi D E ihD ihE =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | pi_domain => exact ihD ((Expr.Subterm.of_child (.pi_domain D E)).trans hn)
        | pi_body => exact ihE ((Expr.Subterm.of_child (.pi_body D E)).trans hn)
  exact aux M hs M (.refl M)
/-- The child hypothesis can equivalently cover every proper syntactic part. -/
theorem induction_descendants {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, (∃ K, Expr.Child K M ∧ Expr.Subterm N K) → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have h : Q M ∧ ∀ N, Expr.Subterm N M → Q N := by
    apply induction_subterms (Q := fun M => Q M ∧ ∀ N, Expr.Subterm N M → Q N) _ hs
    intro M hM hr hc
    have hq : Q M := step M hM (fun N h => (hr N h).1) (by
      rintro N ⟨K,hK,hN⟩
      exact (hc K hK).2 N hN)
    refine ⟨hq, ?_⟩
    intro N hN
    cases hN with
    | refl => exact hq
    | tail hN hK => exact (hc _ hK).2 _ hN
  exact h.1
end StronglyNormalizing
end PureTypeSystem

end OAI
