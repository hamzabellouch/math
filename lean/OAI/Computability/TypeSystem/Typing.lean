import OAI.Computability.TypeSystem.Reduction

namespace OAI

namespace PureTypeSystem

universe u

/-- A declaration's type viewed in the full newest-first context. -/
inductive Lookup {S : Type u} : List (Expr S) → Nat → Expr S → Prop
  | zero (A Γ) : Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ n A} (B) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.rename Nat.succ)

namespace HasType

variable {S : Type u} {P : Specification S}

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {s t : S} (hst : P.axioms s t) : HasType P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- Domain generation alone precedes substitution and does not need
any exchange or context-substitution theorem. -/
theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasType P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasType P Γ A (.sort s) := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM

end HasType

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem subst (h : Converts M N) (σ : Nat → Expr S) :
    Converts (M.subst σ) (N.subst σ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.subst σ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename (h : Converts M N) (ρ : Nat → Nat) :
    Converts (M.rename ρ) (N.rename ρ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.rename ρ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

/-- A simultaneous substitution respects each declared variable's exact type.
This is a premise only of the substitution metatheorem, not of the main target. -/
def TypedSubstitution {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasType P Δ (σ n) (A.subst σ)

namespace TypedSubstitution

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitution P (A :: Γ) Δ σ) :
    TypedSubstitution P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitution P Γ Δ σ)
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    TypedSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasType.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasType.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitution

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem subst (h : HasType P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitution P Γ Δ σ) :
    HasType P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasType.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)

end HasType

namespace Expr

variable {S : Type u}

theorem subst_var_rename (M : Expr S) (ρ : Nat → Nat) :
    M.subst (var ∘ ρ) = M.rename ρ := by
  rw [← subst_rename, subst_var]

@[simp] theorem subst_lift_single (M a : Expr S) :
    (M.rename Nat.succ).subst (single a) = M := by
  rw [subst_rename]
  exact subst_var M

end Expr

namespace HasType

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasType P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

end HasType

namespace TypedSubstitution

variable {S : Type u} {P : Specification S}

theorem identity {Γ : List (Expr S)} (hΓ : ValidContext P Γ) :
    TypedSubstitution P Γ Γ Expr.var := by
  intro n A hn
  simpa only [Expr.subst_var] using HasType.lookup hΓ hn

theorem weaken {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) :
    TypedSubstitution P Γ (A :: Γ) (Expr.var ∘ Nat.succ) := by
  intro n B hn
  simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
    (HasType.weaken (HasType.lookup hA.valid hn) hA)

theorem single {Γ : List (Expr S)} {a A : Expr S} (ha : HasType P Γ a A) :
    TypedSubstitution P (A :: Γ) Γ (Expr.single a) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single, Expr.subst_lift_single] using HasType.lookup ha.valid hn

end TypedSubstitution

namespace HasType

section

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem rename {M A : Expr S} (h : HasType P Γ M A)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    HasType P Δ (M.rename ρ) (A.rename ρ) := by
  have hσ : TypedSubstitution P Γ Δ (Expr.var ∘ ρ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ

theorem instantiate {A b B a : Expr S}
    (hb : HasType P (A :: Γ) b B) (ha : HasType P Γ a A) :
    HasType P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TypedSubstitution.single ha)

theorem weaken_under {A D b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    HasType P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasType P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasType.weaken hA hD
  have hσ := (TypedSubstitution.weaken hD).lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

theorem context_head_conversion {A A' b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hA' : HasType P Γ A' (.sort t)) (hc : Converts A A') :
    HasType P (A' :: Γ) b B := by
  have hσ : TypedSubstitution P (A :: Γ) (A' :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ

end

variable {S : Type u} {P : Specification S}

/-- Generation is stated up to conversion, without any functionality premise. -/
def Generation (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t, P.axioms s t ∧ Converts T (.sort t)
  | .app f a => ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam A b => ∃ B s, HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi A B) (.sort s) ∧ Converts T (.pi A B)
  | .pi A B => ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃)

theorem generation {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) : Generation P Γ M T := by
  induction h with
  | ax h => exact ⟨_, h, .refl _⟩
  | var h ih => exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A, hA, hc⟩ := ihM
          exact ⟨_, .succ D hA, hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t', ht, hc⟩ := ihM
          exact ⟨t', ht, hc.rename Nat.succ⟩
      | app f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi A B =>
          obtain ⟨t₁, t₂, t₃, hA, hB, hr, hc⟩ := ihM
          exact ⟨t₁, t₂, t₃, .weaken hA hD, hB.weaken_under hA hD,
            hr, hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_, _, hb, hPi, .refl _⟩
  | application hf ha ihf iha => exact ⟨_, _, hf, ha, .refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D, hD, hd⟩ := ihM
          exact ⟨D, hD, .trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r, hr, hd⟩ := ihM
          exact ⟨r, hr, .trans _ _ _ (.symm _ _ hc) hd⟩
      | app f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasType P Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃) := h.generation

theorem generation_lam {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) :
    ∃ B s, HasType P (A :: Γ) b B ∧ HasType P Γ (.pi A B) (.sort s) ∧
      Converts T (.pi A B) := h.generation

theorem generation_app {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) :
    ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a) := h.generation

/-- Correctness of types, including the unsorted literal-sort alternative. -/
theorem regularity {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    (∃ s, A = .sort s) ∨ (∃ s, HasType P Γ A (.sort s)) := by
  induction h with
  | ax h => exact .inl ⟨_, rfl⟩
  | var h ih => exact .inr ⟨_, .weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := ihM
      · exact .inl ⟨s, rfl⟩
      · exact .inr ⟨s, .weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_, rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_, hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s, heq⟩ | ⟨s, hPi⟩ := ihf
      · cases heq
      · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
        exact .inr ⟨s₂, hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_, hA⟩

theorem product_type_sorted {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasType P Γ M (.pi A B)) : ∃ s, HasType P Γ (.pi A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasType

namespace Converts

variable {S : Type u}

theorem pi {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi A B) (.pi A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem pi_not_sort {A B : Expr S} {s : S} : ¬ Converts (.pi A B) (.sort s) := by
  intro h
  obtain ⟨N, hN, hs⟩ := h.join
  have heq := (Normal.sort s).reduces_eq hs
  obtain ⟨D, E, hDE, _, _⟩ := hN.pi_inv
  cases heq.trans hDE

theorem sort_inj {s t : S} (h : Converts (Expr.sort s) (.sort t)) : s = t :=
  Expr.sort.inj ((Normal.sort s).eq_of_converts (Normal.sort t) h)

theorem instantiate_right {a a' : Expr S} (h : Converts a a') (B : Expr S) :
    Converts (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace HasType

variable {S : Type u} {P : Specification S}

theorem application_type_sorted_aux {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ f a, M = .app f a → ∃ s, HasType P Γ T (.sort s) := by
  induction h with
  | ax h => intro f a heq; cases heq
  | var h ih => intro f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam A b => cases heq
      | pi A B => cases heq
      | app g b =>
          obtain ⟨r, hr⟩ := ihM g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro f a heq; cases heq
  | application hf ha ihf iha =>
      intro f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) : ∃ s, HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux f a rfl

theorem abstraction_type_sorted {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) : ∃ s, HasType P Γ T (.sort s) := by
  obtain ⟨s, hT⟩ | hs := h.regularity
  · obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
    subst T
    exact False.elim (Converts.pi_not_sort (.symm _ _ hc))
  · exact hs

/-- Reconstructing a sorted expression at its original expected type does not
require a sorting of a terminal (unsorted) sort. -/
theorem conversion_from_sort {Γ : List (Expr S)} {M T : Expr S} {s : S}
    (h : HasType P Γ M (.sort s))
    (hT : (∃ t, T = .sort t) ∨ ∃ t, HasType P Γ T (.sort t))
    (hc : Converts T (.sort s)) : HasType P Γ M T := by
  obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hT
  · have heq := hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)

/-- Subject reduction at the exact original type, including binder annotations. -/
theorem subject_reduction {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Beta M N) : HasType P Γ N T := by
  induction hr generalizing Γ T with
  | head A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨hDA, hEB⟩ := hp.product_compatibility
      obtain ⟨t, hA⟩ := hPi.product_domain A B rfl
      have haA := HasType.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : Converts A A' := .rel _ _ hr
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasType.product hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      have hA' := ih hA
      have hB' := hB.context_head_conversion hA hA' (.rel _ _ hr)
      exact (HasType.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      exact (HasType.product hA (ih hB) hrule).conversion_from_sort h.regularity hc

theorem subject_reduces {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Reduces M N) : HasType P Γ N T := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.subject_reduction hr

end HasType

namespace Normal

variable {S : Type u} {M : Expr S}

theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {a b}, Beta a b → Beta (f a) (f b)) (h : Normal (f M)) : Normal M :=
  fun N hN => h (f N) (hf hN)

theorem app_left {f a : Expr S} (h : Normal (.app f a)) : Normal f :=
  of_map Beta.app_left h

theorem app_right {f a : Expr S} (h : Normal (.app f a)) : Normal a :=
  of_map Beta.app_right h

theorem lam_domain {A b : Expr S} (h : Normal (.lam A b)) : Normal A :=
  of_map Beta.lam_domain h

theorem lam_body {A b : Expr S} (h : Normal (.lam A b)) : Normal b :=
  of_map Beta.lam_body h

theorem pi_domain {A B : Expr S} (h : Normal (.pi A B)) : Normal A :=
  of_map Beta.pi_domain h

theorem pi_body {A B : Expr S} (h : Normal (.pi A B)) : Normal B :=
  of_map Beta.pi_body h

theorem pi {A B : Expr S} (hA : Normal A) (hB : Normal B) : Normal (.pi A B) := by
  intro N h
  cases h with
  | pi_domain h => exact hA _ h
  | pi_body h => exact hB _ h

theorem lam {A b : Expr S} (hA : Normal A) (hb : Normal b) : Normal (.lam A b) := by
  intro N h
  cases h with
  | lam_domain h => exact hA _ h
  | lam_body h => exact hb _ h

end Normal

namespace Expr

variable {S : Type u}

/-- Choice of the unique full beta normal form when it exists. The fallback
is irrelevant on legal syntax under the standing system-wide WN hypothesis. -/
noncomputable def normalForm (M : Expr S) : Expr S := by
  classical
  exact if h : WeaklyNormalizing M then Classical.choose h else M

theorem normalForm_spec {M : Expr S} (h : WeaklyNormalizing M) :
    Reduces M M.normalForm ∧ Normal M.normalForm := by
  rw [normalForm, dite_eq_left h]
  exact Classical.choose_spec h

theorem normalForm_eq {M N : Expr S} (hr : Reduces M N) (hn : Normal N) :
    M.normalForm = N := by
  have h : WeaklyNormalizing M := ⟨N, hr, hn⟩
  obtain ⟨hm, hnm⟩ := normalForm_spec h
  exact hnm.eq_of_converts hn (.trans _ _ _ (.symm _ _ hm.converts) hr.converts)

@[simp] theorem normalForm_of_normal {M : Expr S} (h : Normal M) : M.normalForm = M :=
  normalForm_eq .refl h

theorem normalForm_converts {M N : Expr S} (hM : WeaklyNormalizing M)
    (hN : WeaklyNormalizing N) (hc : Converts M N) : M.normalForm = N.normalForm := by
  obtain ⟨hm, hnm⟩ := normalForm_spec hM
  obtain ⟨hn, hnn⟩ := normalForm_spec hN
  exact hnm.eq_of_converts hnn (.trans _ _ _ (.symm _ _ hm.converts)
    (.trans _ _ _ hc hn.converts))

theorem normalForm_pi {A B : Expr S}
    (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B) :
    (Expr.pi A B).normalForm = .pi A.normalForm B.normalForm :=
  normalForm_eq ((normalForm_spec hA).1.pi (normalForm_spec hB).1)
    ((normalForm_spec hA).2.pi (normalForm_spec hB).2)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := hw Γ h.valid M ⟨A, .inl h⟩

theorem type_weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := hw Γ h.valid A ⟨M, .inr h⟩

theorem normalForm (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    HasType P Γ M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

theorem normalize_type (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    HasType P Γ M A.normalForm := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · simpa only [Expr.normalForm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.normalForm hw)
      (Expr.normalForm_spec (h.type_weaklyNormalizing hw)).1.converts

end HasType

/-- The variable-headed spines used by the manuscript. -/
inductive Neutral {S : Type u} : Expr S → Prop
  | var (n) : Neutral (.var n)
  | app {f a} : Neutral f → Neutral (.app f a)

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem sort_cannot_have_product_type {s : S} {A B : Expr S}
    (h : HasType P Γ (.sort s) (.pi A B)) : False := by
  obtain ⟨t, ht, hc⟩ := h.generation
  exact Converts.pi_not_sort hc

theorem product_cannot_have_product_type {A B D E : Expr S}
    (h : HasType P Γ (.pi A B) (.pi D E)) : False := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
  exact Converts.pi_not_sort hc

theorem lambda_cannot_have_sort_type {A b : Expr S} {s : S}
    (h : HasType P Γ (.lam A b) (.sort s)) : False := by
  obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
  exact Converts.pi_not_sort (.symm _ _ hc)

/-- No functionality is needed for neutral uniqueness: the declaration fixes
its head type, and product compatibility fixes every successive codomain. -/
theorem neutral_unique {M A B : Expr S} (hn : Neutral M)
    (hA : HasType P Γ M A) (hB : HasType P Γ M B) : Converts A B := by
  induction hn generalizing A B with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hA.generation
      obtain ⟨E, hE, hcE⟩ := hB.generation
      have heq : D = E := by
        clear hA hB hcD hcE
        induction hD generalizing E with
        | zero A Γ => cases hE; rfl
        | succ C hD ih =>
            cases hE with
            | succ _ hE => exact congrArg (Expr.rename Nat.succ) (ih _ hE)
      subst E
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | @app f a hn ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := hA.generation_app
      obtain ⟨D', E', hf', ha', hc'⟩ := hB.generation_app
      have he := (ih hf hf').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))

theorem normal_shape {M T : Expr S} (h : HasType P Γ M T) (hn : Normal M) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b, M = .lam A b) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s, rfl⟩
  | lam A b ihA ihb => exact .inr (.inr (.inr ⟨A, b, rfl⟩))
  | pi A B ihA ihB => exact .inr (.inr (.inl ⟨A, B, rfl⟩))
  | app f a ihf iha =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, rfl⟩ | hnf | ⟨A, B, rfl⟩ | ⟨A, b, rfl⟩ := ihf hf hn.app_left
      · exact False.elim hf.sort_cannot_have_product_type
      · exact .inr (.inl (.app hnf))
      · exact False.elim hf.product_cannot_have_product_type
      · exact False.elim (hn _ (.head A b a))

theorem sorted_normal_shape {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) (hn : Normal M) :
    (∃ t, M = .sort t) ∨ Neutral M ∨ (∃ A B, M = .pi A B) := by
  obtain h | h | h | ⟨A, b, rfl⟩ := h.normal_shape hn
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact False.elim h.lambda_cannot_have_sort_type

end HasType

/-! Finite syntax-directed typing trees, with all generation witnesses
retained; no functionality or unique sort choices are imposed. -/

inductive TypingTree {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Type u
  | var {Γ n A T} (typing : HasType P Γ (.var n) T)
      (declaration : Lookup Γ n A) (convert : Converts T A) : TypingTree P Γ (.var n) T
  | sort {Γ s t T} (typing : HasType P Γ (.sort s) T)
      (axioms : P.axioms s t) (convert : Converts T (.sort t)) : TypingTree P Γ (.sort s) T
  | product {Γ A B a b c T} (typing : HasType P Γ (.pi A B) T)
      (domain : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) B (.sort b))
      (rule : P.rule a b c) (convert : Converts T (.sort c)) : TypingTree P Γ (.pi A B) T
  | abstraction {Γ A b B a s T} (typing : HasType P Γ (.lam A b) T)
      (annotation : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) b B)
      (product : HasType P Γ (.pi A B) (.sort s)) (convert : Converts T (.pi A B)) :
      TypingTree P Γ (.lam A b) T
  | application {Γ f a A B T} (typing : HasType P Γ (.app f a) T)
      (function : TypingTree P Γ f (.pi A B)) (argument : TypingTree P Γ a A)
      (convert : Converts T (B.instantiate a)) : TypingTree P Γ (.app f a) T

namespace TypingTree
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- Root expected judgment, including the potentially unsorted final sort. -/
theorem typing (t : TypingTree P Γ M T) : HasType P Γ M T := by
  cases t with
  | var h _ _ => exact h
  | sort h _ _ => exact h
  | product h _ _ _ _ => exact h
  | abstraction h _ _ _ _ => exact h
  | application h _ _ _ => exact h

/-- Retarget only the root; all core data and all children are unchanged. -/
def retarget {T' : Expr S} (t : TypingTree P Γ M T)
    (ht : HasType P Γ M T') (hc : Converts T' T) : TypingTree P Γ M T' := by
  cases t with
  | var _ hd he => exact .var ht hd (.trans _ _ _ hc he)
  | sort _ ha he => exact .sort ht ha (.trans _ _ _ hc he)
  | product _ d b hr he => exact .product ht d b hr (.trans _ _ _ hc he)
  | abstraction _ d b hp he => exact .abstraction ht d b hp (.trans _ _ _ hc he)
  | application _ f a he => exact .application ht f a (.trans _ _ _ hc he)

/-- Generation proves existence of finite stored trees without eliminating a
Prop-valued typing derivation into data or assuming unique formation triples. -/
theorem nonempty (h : HasType P Γ M T) : Nonempty (TypingTree P Γ M T) := by
  induction M generalizing Γ T with
  | var n =>
      obtain ⟨A, hd, hc⟩ := h.generation
      exact ⟨.var h hd hc⟩
  | sort s =>
      obtain ⟨t, ha, hc⟩ := h.generation
      exact ⟨.sort h ha hc⟩
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, hr, hc⟩ := h.generation_pi
      exact ⟨.product h (ihA hA).some (ihB hB).some hr hc⟩
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hp, hc⟩ := h.generation_lam
      obtain ⟨a, a', c, hA, _, _, _⟩ := hp.generation_pi
      exact ⟨.abstraction h (ihA hA).some (ihb hb).some hp hc⟩
  | app f a ihf iha =>
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact ⟨.application h (ihf hf).some (iha ha).some hc⟩

noncomputable def ofTyping (h : HasType P Γ M T) : TypingTree P Γ M T := (nonempty h).some

/-- A genuine variable renaming sends declarations to declarations, rather
than merely to terms that happen to have convertible types. -/
def DeclRenaming (Γ Δ : List (Expr S)) (ρ : Nat → Nat) : Prop :=
  ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (A.rename ρ)

namespace DeclRenaming
variable {Δ : List (Expr S)} {ρ : Nat → Nat}
theorem typed (h : DeclRenaming Γ Δ ρ) (hΔ : ValidContext P Δ) :
    ∀ n A, Lookup Γ n A → HasType P Δ (.var (ρ n)) (A.rename ρ) :=
  fun n A hn => HasType.lookup hΔ (h n A hn)

theorem lift (h : DeclRenaming Γ Δ ρ) (A : Expr S) :
    DeclRenaming (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ) := by
  intro n B hn
  cases hn with
  | zero =>
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using Lookup.zero (A.rename ρ) Δ
  | succ _ hn =>
      have hh := Lookup.succ (A.rename ρ) (h _ _ hn)
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using hh
end DeclRenaming

/-- Thinning/reindexing transports every stored witness and preserves the
whole tree shape. Binder annotations are transported too. -/
noncomputable def rename (t : TypingTree P Γ M T) {Δ : List (Expr S)} (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : DeclRenaming Γ Δ ρ) :
    TypingTree P Δ (M.rename ρ) (T.rename ρ) := by
  induction t generalizing Δ ρ with
  | var h hd hc => exact .var (h.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ)
  | sort h ha hc => exact .sort (h.rename hΔ ρ (hρ.typed hΔ)) ha (hc.rename ρ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .product (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) hr (hc.rename ρ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .abstraction (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) (hp.rename hΔ ρ (hρ.typed hΔ)) (hc.rename ρ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.rename hΔ ρ (hρ.typed hΔ)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
      simpa only [Expr.instantiate_rename] using hc.rename ρ

namespace DeclRenaming
variable {Δ : List (Expr S)}
theorem weaken (A : Expr S) : DeclRenaming Γ (A :: Γ) Nat.succ :=
  fun _ _ h => .succ A h
end DeclRenaming

/-- Substitution carries stored trees at all declaration occurrences. -/
abbrev StoredSubstitution (P : Specification S) (Γ Δ : List (Expr S))
    (σ : Nat → Expr S) : Type u :=
  ∀ n A, Lookup Γ n A → TypingTree P Δ (σ n) (A.subst σ)

namespace StoredSubstitution
variable {Δ : List (Expr S)} {σ : Nat → Expr S}
theorem typed (ts : StoredSubstitution P Γ Δ σ) : TypedSubstitution P Γ Δ σ :=
  fun n A hn => (ts n A hn).typing

noncomputable def lift (ts : StoredSubstitution P Γ Δ σ) {A : Expr S} {s : S}
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    StoredSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) :=
  fun n => match n with
  | 0 => fun B hn => by
      have he : B = A.rename Nat.succ := by cases hn; rfl
      have he' : B.subst (Expr.liftSub σ) = (A.subst σ).rename Nat.succ := by
        rw [he,Expr.subst_rename,Expr.rename_subst]
        rfl
      exact .var (he'.symm ▸ HasType.var hA) (.zero _ _) (by rw [he']; exact .refl _)
  | n+1 => fun B hn => by
      let hex : ∃ B', Lookup Γ n B' ∧ B = B'.rename Nat.succ := by
        cases hn with
        | succ _ h => exact ⟨_, h, rfl⟩
      let tt := (ts _ _ hex.choose_spec.1).rename (.cons hA.valid hA) Nat.succ (DeclRenaming.weaken _)
      have he : B.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          B.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]
            rfl
      exact tt.retarget (he.symm ▸ tt.typing) (by rw [he]; exact .refl _)

end StoredSubstitution

/-- Capture-avoiding substitution grafts the given trees at variables. It
retains core choices and recurses through the annotation at each binder. -/
noncomputable def subst (t : TypingTree P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (ts : StoredSubstitution P Γ Δ σ) :
    TypingTree P Δ (M.subst σ) (T.subst σ) := by
  induction t generalizing Δ σ with
  | var h hd hc => exact (ts _ _ hd).retarget (h.subst hΔ σ ts.typed) (hc.subst σ)
  | sort h ha hc => exact .sort (h.subst hΔ σ ts.typed) ha (hc.subst σ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .product (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) hr (hc.subst σ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .abstraction (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) (hp.subst hΔ σ ts.typed) (hc.subst σ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.subst hΔ σ ts.typed) (ihf hΔ σ ts) (iha hΔ σ ts)
      simpa only [Expr.instantiate_subst] using hc.subst σ

end TypingTree

namespace Expr
variable {S : Type u}
def ProperPart (N M : Expr S) : Prop := ∃ K, Child K M ∧ Subterm N K
namespace ProperPart
variable {N M L : Expr S}
theorem child (h : Child N M) : ProperPart N M := ⟨N,h,.refl N⟩
theorem subterm (h : ProperPart N M) : Subterm N M := by
  obtain ⟨K,hK,hN⟩ := h
  exact .tail hN hK
theorem trans_right (h : ProperPart N M) (hML : Subterm M L) : ProperPart N L := by
  induction hML with
  | refl => exact h
  | tail hML hL ih => exact ⟨_,hL,h.subterm.trans hML⟩
theorem trans_left (hNM : Subterm N M) (h : ProperPart M L) : ProperPart N L := by
  obtain ⟨K,hK,hM⟩ := h
  exact ⟨K,hK,hNM.trans hM⟩
end ProperPart
namespace Subterm
variable {M : Expr S}
theorem apps_head (ns : List (Expr S)) : Subterm M (M.apps ns) := by
  induction ns generalizing M with
  | nil => exact .refl M
  | cons n ns ih => exact (of_child (.app_left M n)).trans (ih (M := .app M n))
end Subterm
namespace ProperPart
variable {M n : Expr S} {ns : List (Expr S)}
theorem apps_arg (hn : n ∈ ns) : ProperPart n (M.apps ns) := by
  induction ns generalizing M with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · exact (child (.app_right M n)).trans_right (Subterm.apps_head ns)
    · exact ih hn
end ProperPart
@[simp] theorem subst_apps (M : Expr S) (ns : List (Expr S)) (σ : Nat → Expr S) :
    (M.apps ns).subst σ = (M.subst σ).apps (ns.map (Expr.subst σ)) := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
theorem spine_shape {M T : Expr S} (h : HasType P Γ M T) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b ns, M = (Expr.lam A b).apps ns) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b => exact .inr (.inr (.inr ⟨A,b,[],rfl⟩))
  | pi A B => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
    obtain ⟨D,E,hf,_,_⟩ := h.generation_app
    rcases ihf hf with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
    · exact False.elim hf.sort_cannot_have_product_type
    · exact .inr (.inl (.app hn))
    · exact False.elim hf.product_cannot_have_product_type
    · exact .inr (.inr (.inr ⟨A,b,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩))

theorem app_spine {f a T : Expr S} (h : HasType P Γ (.app f a) T) :
    Neutral f ∨ ∃ D b n ns, Expr.app f a = (Expr.app (.lam D b) n).apps ns := by
  obtain ⟨D,E,hf,_,_⟩ := h.generation_app
  rcases hf.spine_shape with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
  · exact False.elim hf.sort_cannot_have_product_type
  · exact .inl hn
  · exact False.elim hf.product_cannot_have_product_type
  · right
    cases ns with
    | nil => exact ⟨A,b,a,[],rfl⟩
    | cons n ns => exact ⟨A,b,n,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩

theorem apps_head {M T : Expr S} {ns : List (Expr S)} (h : HasType P Γ (M.apps ns) T) :
    ∃ A, HasType P Γ M A := by
  induction ns generalizing M T with
  | nil => exact ⟨T,h⟩
  | cons n ns ih =>
    obtain ⟨A,hA⟩ := ih h
    obtain ⟨D,E,hf,_,_⟩ := hA.generation_app
    exact ⟨_,hf⟩

theorem apps_arg {M T n : Expr S} {ns : List (Expr S)}
    (h : HasType P Γ (M.apps ns) T) (hn : n ∈ ns) : ∃ A, HasType P Γ n A := by
  induction ns generalizing M T with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · obtain ⟨T,hT⟩ := h.apps_head (M := .app M n) (ns := ns)
      obtain ⟨D,E,_,ha,_⟩ := hT.generation_app
      exact ⟨D,ha⟩
    · exact ih h hn
end HasType

/-- The syntactic application principle implying strong normalization.
This principle is proved from candidate interfaces, not assumed
on the PTS normalization theorem. -/
theorem stronglyNormalizing_of_application
    {S : Type u} {P : Specification S}
    (applySN : ∀ {Γ f a D E}, HasType P Γ f (.pi D E) → HasType P Γ a D →
      StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)) :
    SystemStronglyNormalizing P := by
  have typed : ∀ M : Expr S, ∀ {Γ A}, HasType P Γ M A → StronglyNormalizing M := by
    intro M
    induction M with
    | var n => intro Γ A h; exact (Normal.var n).stronglyNormalizing
    | sort s => intro Γ A h; exact (Normal.sort s).stronglyNormalizing
    | app f a ihf iha =>
        intro Γ A h
        obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
        exact applySN hf ha (ihf hf) (iha ha)
    | lam D b ihD ihb =>
        intro Γ A h
        obtain ⟨E, s, hb, hpi, _⟩ := h.generation_lam
        obtain ⟨s₁, s₂, s₃, hD, _, _, _⟩ := hpi.generation_pi
        exact (ihD hD).lam (ihb hb)
    | pi D E ihD ihE =>
        intro Γ A h
        obtain ⟨s₁, s₂, s₃, hD, hE, _, _⟩ := h.generation_pi
        exact (ihD hD).pi (ihE hE)
  intro Γ _ M h
  obtain ⟨A, h | h⟩ := h
  · exact typed M h
  · obtain ⟨s, rfl⟩ | ⟨s, hs⟩ := h.regularity
    · exact (Normal.sort s).stronglyNormalizing
    · exact typed M hs

/-- A failed full-normalization theorem has an exact, well-typed application
counterexample whose two children are already strongly normalizing. -/
theorem exists_bad_application {S : Type u} {P : Specification S}
    (h : ¬ SystemStronglyNormalizing P) :
    ∃ Γ f a D E, HasType P Γ f (.pi D E) ∧ HasType P Γ a D ∧
      StronglyNormalizing f ∧ StronglyNormalizing a ∧ ¬ StronglyNormalizing (.app f a) := by
  classical
  by_contra hn
  apply h
  apply stronglyNormalizing_of_application
  intro Γ f a D E hf ha hfs has
  by_contra hb
  exact hn ⟨Γ, f, a, D, E, hf, ha, hfs, has, hb⟩

namespace Normal

variable {S : Type u}

theorem rename {M : Expr S} (h : Normal M) (ρ : Nat → Nat) :
    Normal (M.rename ρ) := by
  induction M generalizing ρ with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain ρ).pi (ihB h.pi_body _)
  | lam A b ihA ihb => exact (ihA h.lam_domain ρ).lam (ihb h.lam_body _)
  | app f a ihf iha =>
      have hf := ihf h.app_left ρ
      have ha := iha h.app_right ρ
      cases f with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app f b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hf _ hr
          | app_right hr => exact ha _ hr

end Normal

end PureTypeSystem

end OAI
