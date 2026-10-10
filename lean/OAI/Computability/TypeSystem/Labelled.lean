import OAI.Computability.TypeSystem.Typing

namespace OAI

/- Labelled beta reduction retains every annotation.
These are definitions, not an extension of the PTS specification. -/
namespace PureTypeSystem.Labelled

universe u

inductive Mode
  | data
  | proof
  deriving DecidableEq

inductive Label
  | dd
  | dp
  | pp
  deriving DecidableEq

def Label.domain : Label → Mode
  | .dd | .dp => .data
  | .pp => .proof

def Label.result : Label → Mode
  | .dd => .data
  | .dp | .pp => .proof

inductive Expr (S : Type u) : Type u
  | var : Nat → Expr S
  | sort : S → Expr S
  | app : Label → Expr S → Expr S → Expr S
  | lam : Label → Expr S → Expr S → Expr S
  | pi : Label → Expr S → Expr S → Expr S
  deriving DecidableEq

namespace Expr
variable {S : Type u}

abbrev liftRen := PureTypeSystem.Expr.liftRen

def rename (ρ : Nat → Nat) : Expr S → Expr S
  | .var n => .var (ρ n)
  | .sort s => .sort s
  | .app l f a => .app l (rename ρ f) (rename ρ a)
  | .lam l A b => .lam l (rename ρ A) (rename (liftRen ρ) b)
  | .pi l A B => .pi l (rename ρ A) (rename (liftRen ρ) B)

def liftSub (σ : Nat → Expr S) : Nat → Expr S
  | 0 => .var 0
  | n+1 => (σ n).rename Nat.succ

def subst (σ : Nat → Expr S) : Expr S → Expr S
  | .var n => σ n
  | .sort s => .sort s
  | .app l f a => .app l (subst σ f) (subst σ a)
  | .lam l A b => .lam l (subst σ A) (subst (liftSub σ) b)
  | .pi l A B => .pi l (subst σ A) (subst (liftSub σ) B)

def single (a : Expr S) : Nat → Expr S
  | 0 => a
  | n+1 => .var n

def instantiate (b a : Expr S) : Expr S := b.subst (single a)

def erase : Expr S → PureTypeSystem.Expr S
  | .var n => .var n
  | .sort s => .sort s
  | .app _ f a => .app f.erase a.erase
  | .lam _ A b => .lam A.erase b.erase
  | .pi _ A B => .pi A.erase B.erase

@[simp] theorem rename_id (M : Expr S) : M.rename id = M := by
  induction M <;> simp_all [rename, liftRen, PureTypeSystem.Expr.liftRen_id]

theorem rename_comp (M : Expr S) (ρ τ : Nat → Nat) :
    (M.rename τ).rename ρ = M.rename (ρ ∘ τ) := by
  induction M generalizing ρ τ <;>
    simp_all only [rename, Function.comp_apply, PureTypeSystem.Expr.liftRen_comp]

@[simp] theorem subst_var (M : Expr S) : M.subst .var = M := by
  have h : liftSub (var : Nat → Expr S) = var := by funext n; cases n <;> rfl
  induction M <;> simp_all only [subst]

theorem subst_rename (M : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).subst σ = M.subst (σ ∘ ρ) := by
  have h : ∀ (σ : Nat → Expr S) (ρ : Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
    intro σ ρ; funext n; cases n <;> rfl
  induction M generalizing σ ρ <;> simp_all only [rename, subst, Function.comp_apply]

theorem rename_subst (M : Expr S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (M.subst σ).rename ρ = M.subst (fun n => (σ n).rename ρ) := by
  have h : ∀ (ρ : Nat → Nat) (σ : Nat → Expr S),
      (fun n => (liftSub σ n).rename (liftRen ρ)) = liftSub (fun n => (σ n).rename ρ) := by
    intro ρ σ; funext n; cases n with
    | zero => rfl
    | succ n => simp only [liftSub, rename_comp]; rfl
  induction M generalizing ρ σ <;> simp_all only [subst, rename]

theorem subst_subst (M : Expr S) (σ τ : Nat → Expr S) :
    (M.subst τ).subst σ = M.subst (fun n => (τ n).subst σ) := by
  have h : ∀ (σ τ : Nat → Expr S),
      (fun n => (liftSub τ n).subst (liftSub σ)) = liftSub (fun n => (τ n).subst σ) := by
    intro σ τ; funext n; cases n with
    | zero => rfl
    | succ n => simp only [liftSub, subst_rename, rename_subst]; rfl
  induction M generalizing σ τ <;> simp_all only [subst]

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1; funext n; cases n <;> rfl

theorem instantiate_subst (b a : Expr S) (σ : Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [instantiate, subst_subst]
  congr 1; funext n; cases n with
  | zero => rfl
  | succ n => simp only [liftSub, subst_rename]; exact subst_var (σ n)

@[simp] theorem erase_rename (M : Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).erase = M.erase.rename ρ := by
  induction M generalizing ρ <;> simp_all only [rename, erase, PureTypeSystem.Expr.rename]

theorem erase_liftSub (σ : Nat → Expr S) :
    (fun n => (liftSub σ n).erase) = PureTypeSystem.Expr.liftSub (fun n => (σ n).erase) := by
  funext n; cases n <;> simp only [liftSub, erase, erase_rename, PureTypeSystem.Expr.liftSub]

@[simp] theorem erase_subst (M : Expr S) (σ : Nat → Expr S) :
    (M.subst σ).erase = M.erase.subst (fun n => (σ n).erase) := by
  induction M generalizing σ <;> simp_all only [subst, erase, PureTypeSystem.Expr.subst, erase_liftSub]

@[simp] theorem erase_instantiate (b a : Expr S) :
    (b.instantiate a).erase = b.erase.instantiate a.erase := by
  simp only [instantiate, erase_subst, PureTypeSystem.Expr.instantiate]
  congr 1; funext n; cases n <;> rfl

end Expr

inductive Beta {S : Type u} : Expr S → Expr S → Prop
  | head (l A b a) : Beta (.app l (.lam l A b) a) (b.instantiate a)
  | app_left {l f f' a} : Beta f f' → Beta (.app l f a) (.app l f' a)
  | app_right {l f a a'} : Beta a a' → Beta (.app l f a) (.app l f a')
  | lam_domain {l A A' b} : Beta A A' → Beta (.lam l A b) (.lam l A' b)
  | lam_body {l A b b'} : Beta b b' → Beta (.lam l A b) (.lam l A b')
  | pi_domain {l A A' B} : Beta A A' → Beta (.pi l A B) (.pi l A' B)
  | pi_body {l A B B'} : Beta B B' → Beta (.pi l A B) (.pi l A B')

def Converts {S : Type u} : Expr S → Expr S → Prop := Relation.EqvGen Beta
abbrev Reduces {S : Type u} : Expr S → Expr S → Prop := Relation.ReflTransGen Beta

namespace Beta
variable {S : Type u} {M N : Expr S}

theorem rename (h : Beta M N) (ρ : Nat → Nat) : Beta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head l A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Beta.head l (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left h ih => exact .app_left (ih ρ)
  | app_right h ih => exact .app_right (ih ρ)
  | lam_domain h ih => exact .lam_domain (ih ρ)
  | lam_body h ih => exact .lam_body (ih _)
  | pi_domain h ih => exact .pi_domain (ih ρ)
  | pi_body h ih => exact .pi_body (ih _)

theorem subst (h : Beta M N) (σ : Nat → Expr S) : Beta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head l A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Beta.head l (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left h ih => exact .app_left (ih σ)
  | app_right h ih => exact .app_right (ih σ)
  | lam_domain h ih => exact .lam_domain (ih σ)
  | lam_body h ih => exact .lam_body (ih _)
  | pi_domain h ih => exact .pi_domain (ih σ)
  | pi_body h ih => exact .pi_body (ih _)

theorem erase (h : Beta M N) : PureTypeSystem.Beta M.erase N.erase := by
  induction h with
  | head l A b a => simpa only [Expr.erase, Expr.erase_instantiate] using
      (PureTypeSystem.Beta.head A.erase b.erase a.erase)
  | app_left h ih => exact .app_left ih
  | app_right h ih => exact .app_right ih
  | lam_domain h ih => exact .lam_domain ih
  | lam_body h ih => exact .lam_body ih
  | pi_domain h ih => exact .pi_domain ih
  | pi_body h ih => exact .pi_body ih

end Beta

inductive Parallel {S : Type u} : Expr S → Expr S → Prop
  | var (n) : Parallel (.var n) (.var n)
  | sort (s) : Parallel (.sort s) (.sort s)
  | app {l f f' a a'} : Parallel f f' → Parallel a a' →
      Parallel (.app l f a) (.app l f' a')
  | lam {l A A' b b'} : Parallel A A' → Parallel b b' →
      Parallel (.lam l A b) (.lam l A' b')
  | pi {l A A' B B'} : Parallel A A' → Parallel B B' →
      Parallel (.pi l A B) (.pi l A' B')
  | head {l b b' a a'} (A) : Parallel b b' → Parallel a a' →
      Parallel (.app l (.lam l A b) a) (b'.instantiate a')

namespace Parallel

variable {S : Type u} {M N : Expr S}

@[refl] theorem refl (M : Expr S) : Parallel M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ _ ihA ihB => exact .pi ihA ihB

theorem of_beta (h : Beta M N) : Parallel M N := by
  induction h with
  | head l A b a => exact .head A (refl b) (refl a)
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

/-- Complete development contracts only matching-labelled redexes. -/
def develop : Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app l (lam k A b) a =>
      if l = k then (develop b).instantiate (develop a)
      else app l (lam k (develop A) (develop b)) (develop a)
  | app l f a => app l (develop f) (develop a)
  | lam l A b => lam l (develop A) (develop b)
  | pi l A B => pi l (develop A) (develop B)

end Expr

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem triangle (h : Parallel M N) : Parallel N M.develop := by
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | @app l f f' a a' hf ha ihf iha =>
      cases f with
      | var n => exact .app ihf iha
      | sort s => exact .app ihf iha
      | app k f b => exact .app ihf iha
      | pi k A B => exact .app ihf iha
      | lam k A b =>
          by_cases hl : l = k
          · subst k
            cases hf with
            | lam hA hb =>
                cases ihf with
                | lam ihA ihb => simpa only [Expr.develop, ite_eq_left rfl, ite_true] using
                    (Parallel.head (l := l) _ ihb iha)
          · simpa only [Expr.develop, ite_eq_right hl] using (Parallel.app (l := l) ihf iha)
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | head A _ _ ihb iha =>
      simpa only [Expr.develop, ite_eq_left rfl, ite_true] using ihb.instantiate iha

theorem diamond {a b c : Expr S} (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d := ⟨a.develop, hab.triangle, hac.triangle⟩

end Parallel

namespace Reduces

variable {S : Type u} {l : Label} {f f' a a' A A' b b' : Expr S}

theorem app (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app l f a) (.app l f' a') := by
  exact (hf.lift (fun x => Expr.app l x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app l f' x) (fun _ _ h => Beta.app_right h))

theorem lam (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.lam l A b) (.lam l A' b') := by
  exact (hA.lift (fun x => Expr.lam l x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam l A' x) (fun _ _ h => Beta.lam_body h))

theorem pi (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.pi l A b) (.pi l A' b') := by
  exact (hA.lift (fun x => Expr.pi l x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi l A' x) (fun _ _ h => Beta.pi_body h))

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
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _ _)

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

namespace Reduces

variable {S : Type u} {l : Label} {A B N : Expr S}

theorem pi_inv (h : Reduces (.pi l A B) N) :
    ∃ A' B', N = .pi l A' B' ∧ Reduces A A' ∧ Reduces B B' := by
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

theorem product_compatibility {l k : Label} {A B A' B' : Expr S}
    (h : Converts (.pi l A B) (.pi k A' B')) : l = k ∧ Converts A A' ∧ Converts B B' := by
  obtain ⟨T, hT, hT'⟩ := h.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hT.pi_inv
  obtain ⟨D', E', hDE', hA', hB'⟩ := hT'.pi_inv
  have heq := Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨rfl, .trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩

end Converts

inductive HasType {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasType P [] (.sort s) (.sort t)
  | var {Γ A s} : HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasType P Γ M B → HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {l Γ A B s₁ s₂ s₃} : HasType P Γ A (.sort s₁) →
      HasType P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasType P Γ (.pi l A B) (.sort s₃)
  | abstraction {l Γ A b B s} : HasType P (A :: Γ) b B →
      HasType P Γ (.pi l A B) (.sort s) →
      HasType P Γ (.lam l A b) (.pi l A B)
  | application {l Γ f a A B} : HasType P Γ f (.pi l A B) →
      HasType P Γ a A → HasType P Γ (.app l f a) (B.instantiate a)
  | conversion {Γ M A B s} : HasType P Γ M A → HasType P Γ B (.sort s) →
      Converts A B → HasType P Γ M B

inductive ValidContext {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContext P []
  | cons {Γ A s} : ValidContext P Γ → HasType P Γ A (.sort s) →
      ValidContext P (A :: Γ)

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem valid (h : HasType P Γ M A) : ValidContext P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType

namespace Expr
variable {S : Type u}
@[simp] theorem liftSub_zero (σ : Nat → Expr S) : liftSub σ 0 = var 0 := rfl
@[simp] theorem liftSub_succ (σ : Nat → Expr S) (n : Nat) :
    liftSub σ (n+1) = (σ n).rename Nat.succ := rfl
end Expr

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
    ∀ l A B, M = .pi l A B → ∃ s, HasType P Γ A (.sort s) := by
  induction h with
  | ax h => intro l A B heq; cases heq
  | var h ih => intro l A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro l A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app k f a => cases heq
      | lam k D b => cases heq
      | pi k D E =>
          obtain ⟨rfl, rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM k D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro l A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro l A B heq; cases heq
  | application hf ha ihf iha => intro l A B heq; cases heq
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
  | @abstraction l Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ _ rfl
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

end HasType

def Normal {S : Type u} (M : Expr S) : Prop := ∀ N, ¬ Beta M N

namespace Normal

section

variable {S : Type u} {M N : Expr S}

theorem reduces_eq (hM : Normal M) (h : Reduces M N) : M = N := by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))

theorem eq_of_converts (hM : Normal M) (hN : Normal N) (h : Converts M N) : M = N := by
  obtain ⟨K, hMK, hNK⟩ := h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm

end

variable {S : Type u}
theorem var (n : Nat) : Normal (.var n : Expr S) := by intro N h; cases h
theorem sort (s : S) : Normal (.sort s : Expr S) := by intro N h; cases h
end Normal

namespace HasType

variable {S : Type u} {P : Specification S}

/-- Generation is stated up to conversion, without any functionality premise. -/
def Generation (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t, P.axioms s t ∧ Converts T (.sort t)
  | .app l f a => ∃ A B, HasType P Γ f (.pi l A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam l A b => ∃ B s, HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi l A B) (.sort s) ∧ Converts T (.pi l A B)
  | .pi _l A B => ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
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
      | app l f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam l A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi l A B =>
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
      | app l f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam l D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi l D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {l : Label} {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasType P Γ (.pi l A B) T) :
    ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃) := h.generation

theorem generation_lam {l : Label} {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam l A b) T) :
    ∃ B s, HasType P (A :: Γ) b B ∧ HasType P Γ (.pi l A B) (.sort s) ∧
      Converts T (.pi l A B) := h.generation

theorem generation_app {l : Label} {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app l f a) T) :
    ∃ A B, HasType P Γ f (.pi l A B) ∧ HasType P Γ a A ∧
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

theorem product_type_sorted {l : Label} {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasType P Γ M (.pi l A B)) : ∃ s, HasType P Γ (.pi l A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasType

namespace Converts

variable {S : Type u}

theorem pi {l : Label} {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi l A B) (.pi l A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem pi_not_sort {l : Label} {A B : Expr S} {s : S} : ¬ Converts (.pi l A B) (.sort s) := by
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
    ∀ l f a, M = .app l f a → ∃ s, HasType P Γ T (.sort s) := by
  induction h with
  | ax h => intro l f a heq; cases heq
  | var h ih => intro l f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro l f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam l A b => cases heq
      | pi l A B => cases heq
      | app l g b =>
          obtain ⟨r, hr⟩ := ihM l g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro l f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro l f a heq; cases heq
  | application hf ha ihf iha =>
      intro l f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro l f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {l : Label} {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app l f a) T) : ∃ s, HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux l f a rfl

theorem abstraction_type_sorted {l : Label} {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam l A b) T) : ∃ s, HasType P Γ T (.sort s) := by
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
  | head l A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨_, hDA, hEB⟩ := hp.product_compatibility
      obtain ⟨t, hA⟩ := hPi.product_domain l A B rfl
      have haA := HasType.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right l f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain l A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : Converts A A' := .rel _ _ hr
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasType.product (l := l) hA' hB' hrule
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

namespace Converts
variable {S : Type u} {M N : Expr S}
theorem erase (h : Converts M N) : PureTypeSystem.Converts M.erase N.erase := by
  induction h with
  | rel a b h => exact .rel _ _ h.erase
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h h' ih ih' => exact .trans _ _ _ ih ih'
end Converts

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}
theorem erase (h : HasType P Γ M A) :
    PureTypeSystem.HasType P (Γ.map Expr.erase) M.erase A.erase := by
  induction h with
  | ax h => exact .ax h
  | var h ih => simpa only [List.map_cons, Expr.erase, Expr.erase_rename] using
      PureTypeSystem.HasType.var ih
  | weaken h hA ih ihA =>
      simpa only [List.map_cons, Expr.erase_rename] using PureTypeSystem.HasType.weaken ih ihA
  | product hA hB hr ihA ihB => exact .product ihA ihB hr
  | abstraction hb hPi ihb ihPi => exact .abstraction ihb ihPi
  | application hf ha ihf iha =>
      simpa only [Expr.erase, Expr.erase_instantiate] using PureTypeSystem.HasType.application ihf iha
  | conversion h hA hc ih ihA => exact .conversion ih ihA hc.erase
end HasType

/-- Modes are a separate syntax discipline on the labelled PTS. This keeps
metatheory independent of mode well-formedness and proves preservation below. -/
def modeCons (m : Mode) (γ : Nat → Mode) : Nat → Mode
  | 0 => m
  | n+1 => γ n

inductive WellModed {S : Type u} : (Nat → Mode) → Expr S → Mode → Prop
  | var {γ} (n) : WellModed γ (.var n) (γ n)
  | sort {γ} (s) : WellModed γ (.sort s) .data
  | app {γ l f a} : WellModed γ f l.result → WellModed γ a l.domain →
      WellModed γ (.app l f a) l.result
  | lam {γ l A b} : WellModed γ A .data → WellModed (modeCons l.domain γ) b l.result →
      WellModed γ (.lam l A b) l.result
  | pi {γ l A B} : WellModed γ A .data → WellModed (modeCons l.domain γ) B .data →
      WellModed γ (.pi l A B) .data

namespace WellModed
variable {S : Type u} {γ δ : Nat → Mode} {M : Expr S} {m : Mode}
theorem rename (h : WellModed γ M m) (ρ : Nat → Nat) (hρ : ∀ n, δ (ρ n) = γ n) :
    WellModed δ (M.rename ρ) m := by
  have hlift {γ δ : Nat → Mode} (ρ : Nat → Nat) (hρ : ∀ n, δ (ρ n) = γ n)
      (i : Mode) : ∀ n, modeCons i δ (Expr.liftRen ρ n) = modeCons i γ n := by
    intro n; cases n with
    | zero => rfl
    | succ n => exact hρ n
  induction h generalizing δ ρ with
  | var n => simpa only [Expr.rename, hρ n] using WellModed.var (γ := δ) (ρ n)
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf ρ hρ) (iha ρ hρ)
  | lam hA hb ihA ihb => exact .lam (ihA ρ hρ) (ihb _ (hlift ρ hρ _))
  | pi hA hB ihA ihB => exact .pi (ihA ρ hρ) (ihB _ (hlift ρ hρ _))

theorem subst (h : WellModed γ M m) (σ : Nat → Expr S)
    (hσ : ∀ n, WellModed δ (σ n) (γ n)) : WellModed δ (M.subst σ) m := by
  have hlift {γ δ : Nat → Mode} (σ : Nat → Expr S)
      (hσ : ∀ n, WellModed δ (σ n) (γ n)) (i : Mode) :
      ∀ n, WellModed (modeCons i δ) (Expr.liftSub σ n) (modeCons i γ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hσ n).rename Nat.succ (fun _ => rfl)
  induction h generalizing δ σ with
  | var n => exact hσ n
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf σ hσ) (iha σ hσ)
  | lam hA hb ihA ihb => exact .lam (ihA σ hσ) (ihb _ (hlift σ hσ _))
  | pi hA hB ihA ihB => exact .pi (ihA σ hσ) (ihB _ (hlift σ hσ _))

theorem instantiate {i : Mode} {b a : Expr S}
    (hb : WellModed (modeCons i γ) b m) (ha : WellModed γ a i) :
    WellModed γ (b.instantiate a) m := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

theorem beta {N : Expr S} (h : WellModed γ M m) (hr : Beta M N) : WellModed γ N m := by
  induction hr generalizing γ m with
  | head l A b a =>
      cases h with
      | app hf ha => cases hf with
        | lam hA hb => exact hb.instantiate ha
  | app_left hr ih => cases h with | app hf ha => exact .app (ih hf) ha
  | app_right hr ih => cases h with | app hf ha => exact .app hf (ih ha)
  | lam_domain hr ih => cases h with | lam hA hb => exact .lam (ih hA) hb
  | lam_body hr ih => cases h with | lam hA hb => exact .lam hA (ih hb)
  | pi_domain hr ih => cases h with | pi hA hB => exact .pi (ih hA) hB
  | pi_body hr ih => cases h with | pi hA hB => exact .pi hA (ih hB)

theorem reduces {N : Expr S} (h : WellModed γ M m) (hr : Reduces M N) : WellModed γ N m := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr
end WellModed

namespace Expr
variable {S : Type u}
theorem erase_lam_inv {M : Expr S} {D e : PureTypeSystem.Expr S}
    (h : M.erase = .lam D e) :
    ∃ l A b, M = .lam l A b ∧ A.erase = D ∧ b.erase = e := by
  cases M with
  | var n => cases h
  | sort s => cases h
  | app l f a => cases h
  | pi l A B => cases h
  | lam l A b =>
      have hh := PureTypeSystem.Expr.lam.inj h
      exact ⟨l, A, b, rfl, hh.1, hh.2⟩
end Expr

private theorem erased_app_step {S : Type u} {f a N : PureTypeSystem.Expr S}
    (h : PureTypeSystem.Beta (.app f a) N) :
    (∃ D b, f = .lam D b ∧ N = b.instantiate a) ∨
    (∃ f', PureTypeSystem.Beta f f' ∧ N = .app f' a) ∨
    (∃ a', PureTypeSystem.Beta a a' ∧ N = .app f a') := by
  cases h with
  | head D b a => exact .inl ⟨D, b, rfl, rfl⟩
  | app_left h => exact .inr (.inl ⟨_, h, rfl⟩)
  | app_right h => exact .inr (.inr ⟨_, h, rfl⟩)

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- Every erased redex of a typable labelled term has matching labels, even
inside its annotations. No weak or strong normalization is assumed. -/
theorem lift_erased_step (h : HasType P Γ M T) {N : PureTypeSystem.Expr S}
    (hr : PureTypeSystem.Beta M.erase N) :
    ∃ M', Beta M M' ∧ M'.erase = N := by
  induction M generalizing Γ T N with
  | var n => cases hr
  | sort s => cases hr
  | app l f a ihf iha =>
      obtain ⟨A, B, hf, ha, _⟩ := h.generation_app
      obtain ⟨D, b, he, rfl⟩ | ⟨f', hstep, rfl⟩ | ⟨a', hstep, rfl⟩ := erased_app_step hr
      · obtain ⟨k, D', b', rfl, _, hb'⟩ := Expr.erase_lam_inv he
        obtain ⟨B', _, _, _, hc⟩ := hf.generation_lam
        have hl := hc.product_compatibility.1
        subst k
        refine ⟨b'.instantiate a, .head l D' b' a, ?_⟩
        simp only [Expr.erase_instantiate, hb']
      · obtain ⟨g, hg, he⟩ := ihf hf hstep
        exact ⟨.app l g a, .app_left hg, by simp only [Expr.erase, he]⟩
      · obtain ⟨b, hb, he⟩ := iha ha hstep
        exact ⟨.app l f b, .app_right hb, by simp only [Expr.erase, he]⟩
  | lam l A b ihA ihb =>
      obtain ⟨B, _, hb, hPi, _⟩ := h.generation_lam
      obtain ⟨s, hA⟩ := hPi.product_domain _ _ _ rfl
      cases hr with
      | lam_domain hstep =>
          obtain ⟨D, hD, he⟩ := ihA hA hstep
          exact ⟨.lam l D b, .lam_domain hD, by simp only [Expr.erase, he]⟩
      | lam_body hstep =>
          obtain ⟨e, he, herase⟩ := ihb hb hstep
          exact ⟨.lam l A e, .lam_body he, by simp only [Expr.erase, herase]⟩
  | pi l A B ihA ihB =>
      obtain ⟨_, _, _, hA, hB, _, _⟩ := h.generation_pi
      cases hr with
      | pi_domain hstep =>
          obtain ⟨D, hD, he⟩ := ihA hA hstep
          exact ⟨.pi l D B, .pi_domain hD, by simp only [Expr.erase, he]⟩
      | pi_body hstep =>
          obtain ⟨E, hE, he⟩ := ihB hB hstep
          exact ⟨.pi l A E, .pi_body hE, by simp only [Expr.erase, he]⟩

theorem lift_erased_reduces (h : HasType P Γ M T) {N : PureTypeSystem.Expr S}
    (hr : PureTypeSystem.Reduces M.erase N) :
    ∃ M', Reduces M M' ∧ M'.erase = N ∧ HasType P Γ M' T := by
  induction hr with
  | refl => exact ⟨M, .refl, rfl, h⟩
  | tail hred hstep ih =>
      obtain ⟨M', hMM', he, ht⟩ := ih
      obtain ⟨M'', hM'M'', he'⟩ := ht.lift_erased_step (he ▸ hstep)
      exact ⟨M'', hMM'.tail hM'M'', he', ht.subject_reduction hM'M''⟩

/-- The exact final interface of the labelled-metatheory lemma. -/
theorem normal_erasure_reduct (h : HasType P Γ M T) {γ : Nat → Mode} {m : Mode}
    (hm : WellModed γ M m) (hw : PureTypeSystem.WeaklyNormalizing M.erase) :
    ∃ M', Reduces M M' ∧ HasType P Γ M' T ∧ WellModed γ M' m ∧
      PureTypeSystem.Normal M'.erase := by
  obtain ⟨N, hr, hn⟩ := hw
  obtain ⟨M', hMM', he, ht⟩ := h.lift_erased_reduces hr
  exact ⟨M', hMM', ht, hm.reduces hMM', he.symm ▸ hn⟩
end HasType

namespace Expr
variable {S : Type u}
def weight : Expr S → Nat
  | .var _ | .sort _ => 1
  | .app _ f a => 1 + f.weight + a.weight
  | .lam _ A b => 1 + A.weight + b.weight
  | .pi _ A B => 1 + A.weight + B.weight

/-- A terminal contains data/data labels only. -/
inductive AllData : Expr S → Prop
  | var (n) : AllData (.var n)
  | sort (s) : AllData (.sort s)
  | app {f a} : AllData f → AllData a → AllData (.app .dd f a)
  | lam {A b} : AllData A → AllData b → AllData (.lam .dd A b)
  | pi {A B} : AllData A → AllData B → AllData (.pi .dd A B)

namespace AllData
theorem rename {M : Expr S} (h : AllData M) (ρ : Nat → Nat) : AllData (M.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam hA hb ihA ihb => exact .lam (ihA ρ) (ihb _)
  | pi hA hB ihA ihB => exact .pi (ihA ρ) (ihB _)
end AllData

/-- A positive telescope ending in an all-data terminal. The source uses
constant telescopes; the no-normal-proof argument also permits dependency. -/
inductive Positive : Expr S → Prop
  | terminal {T} : AllData T → Positive T
  | step (D) {E} : Positive E → Positive (.pi .dp D E)

namespace Positive
theorem rename {M : Expr S} (h : Positive M) (ρ : Nat → Nat) : Positive (M.rename ρ) := by
  induction h generalizing ρ with
  | terminal h => exact .terminal (h.rename ρ)
  | step D h ih => exact .step _ (ih _)

theorem not_pp {A B : Expr S} : ¬ Positive (.pi .pp A B) := by
  intro h
  cases h with
  | terminal h => cases h

theorem dp_body {A B : Expr S} (h : Positive (.pi .dp A B)) : Positive B := by
  cases h with
  | terminal h => cases h
  | step A h => exact h
end Positive

/-- The normal target family used in the no-normal-proof obstruction. -/
def Target (T : Expr S) : Prop := Positive T ∧ PureTypeSystem.Normal T.erase

namespace Target
theorem rename {T : Expr S} (h : Target T) (ρ : Nat → Nat) : Target (T.rename ρ) :=
  ⟨h.1.rename ρ, by simpa only [erase_rename] using h.2.rename ρ⟩

theorem normal {T : Expr S} (h : Target T) : Normal T :=
  fun N hN => h.2 N.erase hN.erase

theorem product {l : Label} {A B T : Expr S} (h : Target T)
    (hl : l.result = .proof) (hc : Converts (.pi l A B) T) :
    l = .dp ∧ ∃ D E, T = .pi .dp D E ∧ Target E ∧ Converts A D ∧ Converts B E := by
  obtain ⟨N, hPi, hT⟩ := hc.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hPi.pi_inv
  have he : T = .pi l D E := (h.normal.reduces_eq hT).trans hDE
  subst T
  cases l with
  | dd => cases hl
  | pp => exact False.elim (Positive.not_pp h.1)
  | dp =>
      exact ⟨rfl, D, E, rfl, ⟨h.1.dp_body, h.2.pi_body⟩, hA.converts, hB.converts⟩
end Target

inductive Neutral : Expr S → Prop
  | var (n) : Neutral (.var n)
  | app {l f a} : Neutral f → Neutral (.app l f a)
end Expr

namespace WellModed
variable {S : Type u} {γ : Nat → Mode} {m : Mode}
theorem var_inv {n} (h : WellModed (S := S) γ (.var n) m) : γ n = m := by
  cases h; rfl

theorem app_inv {l f a} (h : WellModed (S := S) γ (.app l f a) m) :
    l.result = m ∧ WellModed γ f l.result ∧ WellModed γ a l.domain := by
  cases h; exact ⟨rfl, ‹_›, ‹_›⟩

theorem lam_inv {l A b} (h : WellModed (S := S) γ (.lam l A b) m) :
    l.result = m ∧ WellModed γ A .data ∧ WellModed (modeCons l.domain γ) b l.result := by
  cases h; exact ⟨rfl, ‹_›, ‹_›⟩

/-- A normal-erasure proof has a lambda at the root or a variable-headed spine. -/
theorem normal_proof_shape {M : Expr S} (h : WellModed γ M .proof)
    (hn : PureTypeSystem.Normal M.erase) :
    (∃ l A b, M = .lam l A b) ∨ M.Neutral := by
  induction M generalizing γ with
  | var n => exact .inr (.var n)
  | sort s => cases h
  | pi l A B ihA ihB => cases h
  | lam l A b ihA ihb => exact .inl ⟨_, _, _, rfl⟩
  | app l f a ihf iha =>
      obtain ⟨hl, hf, _⟩ := h.app_inv
      obtain ⟨k, A, b, rfl⟩ | hf' := ihf (hl ▸ hf) hn.app_left
      · exact False.elim (hn _ (.head A.erase b.erase a.erase))
      · exact .inr (.app hf')
end WellModed

/-- Only proof variables are constrained. Each is a proof/proof converter
whose first argument is one of the positive normal targets. This includes
exactly the context shape used by the source, and is stable under data
extensions. No converter result is assumed inhabited. -/
def ProofContext {S : Type u} (Γ : List (Expr S)) (γ : Nat → Mode) : Prop :=
  ∀ n A, Lookup Γ n A → γ n = .proof →
    ∃ R F, A = .pi .pp R F ∧ R.Target

namespace ProofContext
variable {S : Type u} {Γ : List (Expr S)} {γ : Nat → Mode}
theorem data_cons (h : ProofContext Γ γ) (D : Expr S) :
    ProofContext (D :: Γ) (modeCons .data γ) := by
  intro n A hn hm
  cases hn with
  | zero => cases hm
  | succ D hn =>
      obtain ⟨R, F, rfl, hR⟩ := h _ _ hn hm
      exact ⟨R.rename Nat.succ, F.rename (Expr.liftRen Nat.succ), rfl, hR.rename _⟩
end ProofContext

namespace Expr.Neutral
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {M T : Expr S}

/-- The first argument of a normal proof-mode converter spine is itself a
strictly smaller normal proof at a positive target. -/
theorem first_target (hM : M.Neutral) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : PureTypeSystem.Normal M.erase)
    (hΓ : ProofContext Γ γ) :
    (∃ n, M = .var n) ∨
    ∃ Q R, Q.weight < M.weight ∧ R.Target ∧ HasType P Γ Q R ∧
      WellModed γ Q .proof ∧ PureTypeSystem.Normal Q.erase := by
  induction hM generalizing T with
  | var n => exact .inl ⟨n, rfl⟩
  | @app l f a hM ih =>
      obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
      obtain ⟨hl, hmf, hma⟩ := hm.app_inv
      have hmf' : WellModed γ f .proof := hl ▸ hmf
      obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ := ih hf hmf' hn.app_left
      · obtain ⟨A, hlookup, hc⟩ := hf.generation
        obtain ⟨R, F, rfl, hR⟩ := hΓ n A hlookup hmf'.var_inv
        obtain ⟨rfl, hDR, _⟩ := hc.product_compatibility
        obtain ⟨r, hPi⟩ := (HasType.lookup h.valid hlookup).product_type_sorted
        obtain ⟨s, hs⟩ := hPi.product_domain _ _ _ rfl
        exact .inr ⟨a, R, by simp only [weight]; omega, hR,
          .conversion ha hs hDR, hma, hn.app_right⟩
      · exact .inr ⟨Q, R, by simp only [weight]; omega, hR, hQR, hmode, hnorm⟩
end Expr.Neutral

/-- No normal erasure at a terminal. The stronger form allows a dependent
positive telescope: it uses only the outer labels, normality, typing and
the decreasing body/first-argument syntax measure. -/
theorem no_normal_proof {S : Type u} {P : Specification S}
    {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}
    (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : PureTypeSystem.Normal M.erase) : False := by
  induction M using (measure Expr.weight).wf.induction generalizing Γ γ T with
  | h M ih =>
      obtain ⟨l, A, b, rfl⟩ | hneutral := hm.normal_proof_shape hn
      · obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
        obtain ⟨hl, _, hmb⟩ := hm.lam_inv
        obtain ⟨rfl, D, E, rfl, hE, hAD, hBE⟩ := hT.product hl (.symm _ _ hc)
        obtain ⟨r, hTsort⟩ := h.abstraction_type_sorted
        obtain ⟨_, _, _, hD, hEopen, _, _⟩ := hTsort.generation_pi
        obtain ⟨_, hA⟩ := hPi.product_domain _ _ _ rfl
        have hEsort := hEopen.context_head_conversion hD hA (.symm _ _ hAD)
        have hbody := HasType.conversion hb hEsort hBE
        exact ih b (by change b.weight < 1 + A.weight + b.weight; omega)
          (hΓ.data_cons A) hE hbody hmb hn.lam_body
      · obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ :=
          hneutral.first_target h hm hn hΓ
        · obtain ⟨A, hlookup, hc⟩ := h.generation
          obtain ⟨R, F, rfl, _⟩ := hΓ n A hlookup hm.var_inv
          have hl := (hT.product rfl (.symm _ _ hc)).1
          cases hl
        · exact ih Q hQ hΓ hR hQR hmode hnorm

/-- A system-wide WN PTS has no proof-mode inhabitant of these targets in
these converter contexts. All later encodings must supply a genuine typing
and mode derivation to invoke this obstruction. -/
theorem no_proof_at_target {S : Type u} {P : Specification S}
    (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}
    (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) : False := by
  obtain ⟨M', _, ht, hmode, hnorm⟩ := h.normal_erasure_reduct hm (h.erase.weaklyNormalizing hw)
  exact no_normal_proof hΓ hT ht hmode hnorm

end PureTypeSystem.Labelled

end OAI
