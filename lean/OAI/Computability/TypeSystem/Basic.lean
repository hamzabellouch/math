import Mathlib

namespace OAI

/-!
Full annotated PTS syntax, modulo alpha-renaming via de Bruijn indices.
Contexts are stored newest-first, each declaration in its prefix context.
No functionality assumptions on axioms or product rules.
-/

namespace PureTypeSystem

universe u

inductive Expr (Sorts : Type u) : Type u
  | var : Nat → Expr Sorts
  | sort : Sorts → Expr Sorts
  | app : Expr Sorts → Expr Sorts → Expr Sorts
  | lam : Expr Sorts → Expr Sorts → Expr Sorts
  | pi : Expr Sorts → Expr Sorts → Expr Sorts
  deriving DecidableEq

namespace Expr

variable {S : Type u}

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def rename (ρ : Nat → Nat) : Expr S → Expr S
  | var n => var (ρ n)
  | sort s => sort s
  | app f a => app (rename ρ f) (rename ρ a)
  | lam A b => lam (rename ρ A) (rename (liftRen ρ) b)
  | pi A B => pi (rename ρ A) (rename (liftRen ρ) B)

def liftSub (σ : Nat → Expr S) : Nat → Expr S
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

def subst (σ : Nat → Expr S) : Expr S → Expr S
  | var n => σ n
  | sort s => sort s
  | app f a => app (subst σ f) (subst σ a)
  | lam A b => lam (subst σ A) (subst (liftSub σ) b)
  | pi A B => pi (subst σ A) (subst (liftSub σ) B)

def single (a : Expr S) : Nat → Expr S
  | 0 => a
  | n + 1 => var n

def instantiate (b a : Expr S) : Expr S := subst (single a) b

end Expr

structure Specification (S : Type u) where
  axioms : S → S → Prop
  rule : S → S → S → Prop

inductive Beta {S : Type u} : Expr S → Expr S → Prop
  | head (A b a) : Beta (.app (.lam A b) a) (b.instantiate a)
  | app_left {f f' a} : Beta f f' → Beta (.app f a) (.app f' a)
  | app_right {f a a'} : Beta a a' → Beta (.app f a) (.app f a')
  | lam_domain {A A' b} : Beta A A' → Beta (.lam A b) (.lam A' b)
  | lam_body {A b b'} : Beta b b' → Beta (.lam A b) (.lam A b')
  | pi_domain {A A' B} : Beta A A' → Beta (.pi A B) (.pi A' B)
  | pi_body {A B B'} : Beta B B' → Beta (.pi A B) (.pi A B')

def Converts {S : Type u} : Expr S → Expr S → Prop := Relation.EqvGen Beta

def Normal {S : Type u} (M : Expr S) : Prop := ∀ N, ¬ Beta M N

def WeaklyNormalizing {S : Type u} (M : Expr S) : Prop :=
  ∃ N, Relation.ReflTransGen Beta M N ∧ Normal N

/-- Accessibility for the converse of reduction: strong normalization,
including reductions in all type annotations. -/
def StronglyNormalizing {S : Type u} (M : Expr S) : Prop :=
  Acc (fun N M : Expr S => Beta M N) M

inductive HasType {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasType P [] (.sort s) (.sort t)
  | var {Γ A s} : HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasType P Γ M B → HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasType P Γ A (.sort s₁) →
      HasType P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasType P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasType P (A :: Γ) b B →
      HasType P Γ (.pi A B) (.sort s) →
      HasType P Γ (.lam A b) (.pi A B)
  | application {Γ f a A B} : HasType P Γ f (.pi A B) →
      HasType P Γ a A → HasType P Γ (.app f a) (B.instantiate a)
  | conversion {Γ M A B s} : HasType P Γ M A → HasType P Γ B (.sort s) →
      Converts A B → HasType P Γ M B

inductive ValidContext {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContext P []
  | cons {Γ A s} : ValidContext P Γ → HasType P Γ A (.sort s) →
      ValidContext P (A :: Γ)

def Legal {S : Type u} (P : Specification S) (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ A, HasType P Γ M A ∨ HasType P Γ A M

def SystemWeaklyNormalizing {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → WeaklyNormalizing M

def SystemStronglyNormalizing {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → StronglyNormalizing M


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

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_succ (ρ : Nat → Nat) (n : Nat) :
    liftRen ρ (n + 1) = ρ n + 1 := rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n
  cases n <;> rfl

theorem liftRen_comp (ρ τ : Nat → Nat) : liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext n
  cases n <;> rfl

@[simp] theorem rename_id (M : Expr S) : rename id M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename, ihf, iha]
  | lam A b ihA ihb => simp [rename, ihA, ihb]
  | pi A B ihA ihB => simp [rename, ihA, ihB]

theorem rename_comp (M : Expr S) (ρ τ : Nat → Nat) :
    rename ρ (rename τ M) = rename (ρ ∘ τ) M := by
  induction M generalizing ρ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | lam A b ihA ihb => simp only [rename, ihA, ihb, liftRen_comp]
  | pi A B ihA ihB => simp only [rename, ihA, ihB, liftRen_comp]

@[simp] theorem liftSub_zero (σ : Nat → Expr S) : liftSub σ 0 = var 0 := rfl
@[simp] theorem liftSub_succ (σ : Nat → Expr S) (n : Nat) :
    liftSub σ (n + 1) = rename Nat.succ (σ n) := rfl

@[simp] theorem liftSub_var : liftSub (var : Nat → Expr S) = var := by
  funext n
  cases n <;> rfl

@[simp] theorem subst_var (M : Expr S) : subst var M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | lam A b ihA ihb => simp [subst, ihA, ihb]
  | pi A B ihA ihB => simp [subst, ihA, ihB]

theorem subst_rename (M : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    subst σ (rename ρ M) = subst (σ ∘ ρ) M := by
  have hlift : ∀ (σ : Nat → Expr S) (ρ : Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
    intro σ ρ
    funext n
    cases n <;> rfl
  induction M generalizing σ ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | lam A b ihA ihb => simp only [rename, subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [rename, subst, ihA, ihB, hlift]

theorem rename_subst (M : Expr S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    rename ρ (subst σ M) = subst (fun n => rename ρ (σ n)) M := by
  have hlift : ∀ (ρ : Nat → Nat) (σ : Nat → Expr S),
      (fun n => rename (liftRen ρ) (liftSub σ n)) =
        liftSub (fun n => rename ρ (σ n)) := by
    intro ρ σ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, rename_comp]
        rfl
  induction M generalizing ρ σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, rename, ihf, iha]
  | lam A b ihA ihb => simp only [subst, rename, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, rename, ihA, ihB, hlift]

theorem subst_subst (M : Expr S) (σ τ : Nat → Expr S) :
    subst σ (subst τ M) = subst (fun n => subst σ (τ n)) M := by
  have hlift : ∀ (σ τ : Nat → Expr S),
      (fun n => subst (liftSub σ) (liftSub τ n)) =
        liftSub (fun n => subst σ (τ n)) := by
    intro σ τ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, subst_rename, rename_subst]
        rfl
  induction M generalizing σ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | lam A b ihA ihb => simp only [subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, ihA, ihB, hlift]

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem instantiate_subst (b a : Expr S) (σ : Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [instantiate, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [liftSub_succ, subst_rename]
      exact subst_var (σ n)

end Expr

namespace Beta

variable {S : Type u} {M N : Expr S}

theorem rename (h : Beta M N) (ρ : Nat → Nat) : Beta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Beta.head (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left _ ih => exact .app_left (ih ρ)
  | app_right _ ih => exact .app_right (ih ρ)
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftRen ρ))
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftRen ρ))

theorem subst (h : Beta M N) (σ : Nat → Expr S) : Beta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Beta.head (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left _ ih => exact .app_left (ih σ)
  | app_right _ ih => exact .app_right (ih σ)
  | lam_domain _ ih => exact .lam_domain (ih σ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftSub σ))
  | pi_domain _ ih => exact .pi_domain (ih σ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftSub σ))

end Beta

end PureTypeSystem

end OAI
