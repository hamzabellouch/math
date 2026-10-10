import Mathlib
import OAI.Computability.Interspersed.Machines
import OAI.Computability.Interspersed.Stacks

namespace OAI

/-! Reversible interspersed-history instruction cylinders. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Interspersed
inductive Control (Q : Type*) where
  | main (q : Q) (incoming : Move)
  | scanRight (q : Q)
  | scanLeft (q : Q)
  deriving DecidableEq

 

abbrev Record (Q A : Type*) (H : Set Q) := {q : Q // q ∉ H} × Move × A
abbrev Symbol (Q A : Type*) (H : Set Q) := A ⊕ Record Q A H
abbrev Config (Q A : Type*) (H : Set Q) :=
  Control Q × Stack (Symbol Q A H) × Stack (Symbol Q A H)

 

inductive Branch (Q A : Type*) (H : Set Q) where
  | main (q : {q : Q // q ∉ H}) (incoming : Move) (a : A)
  | rightRecord (q : Q) (g : Record Q A H)
  | rightWork (q : Q) (a : A)
  | leftRecord (q : Q) (g : Record Q A H)
  | leftWork (q : Q) (a : A)

variable {Q A : Type*} {H : Set Q}

 
def source (r : Branch Q A H) (L R : Stack (Symbol Q A H)) : Config Q A H :=
  match r with
  | .main q h a => (.main q h, L, push (.inl a) R)
  | .rightRecord q g => (.scanRight q, L, push (.inr g) R)
  | .rightWork q a => (.scanRight q, L, push (.inl a) R)
  | .leftRecord q g => (.scanLeft q, push (.inr g) L, R)
  | .leftWork q a => (.scanLeft q, push (.inl a) L, R)

 

def target (δ : Q → A → Q × A × Move) (r : Branch Q A H)
    (L R : Stack (Symbol Q A H)) : Config Q A H :=
  match r with
  | .main q h a =>
    let (q', b, d) := δ q a
    let g : Record Q A H := (q, h, a)
    match d with
    | .stay => (.main q' .stay, push (.inr g) L, push (.inl b) R)
    | .right => (.scanRight q', push (.inl b) (push (.inr g) L), R)
    | .left => (.scanLeft q', L, push (.inl b) (push (.inr g) R))
  | .rightRecord q g => (.scanRight q, push (.inr g) L, R)
  | .rightWork q a => (.main q .right, L, push (.inl a) R)
  | .leftRecord q g => (.scanLeft q, L, push (.inr g) R)
  | .leftWork q a => (.main q .left, L, push (.inl a) R)

 

theorem source_unique {r s : Branch Q A H} {L R L' R' : Stack (Symbol Q A H)}
    (h : source r L R = source s L' R') : r = s ∧ L = L' ∧ R = R' := by
  cases r <;> cases s <;> simp_all [source, push_inj, Subtype.ext_iff]

 

theorem target_unique (δ : Q → A → Q × A × Move)
    {r s : Branch Q A H} {L R L' R' : Stack (Symbol Q A H)}
    (h : target δ r L R = target δ s L' R') : r = s ∧ L = L' ∧ R = R' := by
  cases r <;> cases s <;> simp only [target] at h
  all_goals (repeat' (split at h)) <;> simp_all [push_inj, Subtype.ext_iff]

 
def sourceCylinder (r : Branch Q A H) : Set (Config Q A H) :=
  {c | ∃ L R, source r L R = c}

 
def imageCylinder (δ : Q → A → Q × A × Move) (r : Branch Q A H) :
    Set (Config Q A H) :=
  {c | ∃ L R, target δ r L R = c}

theorem source_cylinders_disjoint {r s : Branch Q A H} (hrs : r ≠ s) :
    Disjoint (sourceCylinder r) (sourceCylinder s) := by
  rw [Set.disjoint_left]
  rintro c ⟨L, R, h⟩ ⟨L', R', h'⟩
  exact hrs (source_unique (h.trans h'.symm)).1

theorem image_cylinders_disjoint (δ : Q → A → Q × A × Move)
    {r s : Branch Q A H} (hrs : r ≠ s) :
    Disjoint (imageCylinder δ r) (imageCylinder δ s) := by
  rw [Set.disjoint_left]
  rintro c ⟨L, R, h⟩ ⟨L', R', h'⟩
  exact hrs (target_unique δ (h.trans h'.symm)).1

 
def Step (δ : Q → A → Q × A × Move) (c d : Config Q A H) : Prop :=
  ∃ r L R, source r L R = c ∧ target δ r L R = d

theorem Step.of_branch (δ : Q → A → Q × A × Move) (r : Branch Q A H)
    (L R : Stack (Symbol Q A H)) : Step δ (source r L R) (target δ r L R) :=
  ⟨r, L, R, rfl, rfl⟩

theorem Step.deterministic {δ : Q → A → Q × A × Move}
    {c d e : Config Q A H} (h : Step δ c d) (h' : Step δ c e) : d = e := by
  rcases h with ⟨r, L, R, hs, ht⟩
  rcases h' with ⟨s, L', R', hs', ht'⟩
  rcases source_unique (hs.trans hs'.symm) with ⟨rfl, rfl, rfl⟩
  exact ht.symm.trans ht'

theorem Step.injective {δ : Q → A → Q × A × Move}
    {c d e : Config Q A H} (h : Step δ c e) (h' : Step δ d e) : c = d := by
  rcases h with ⟨r, L, R, hs, ht⟩
  rcases h' with ⟨s, L', R', hs', ht'⟩
  rcases target_unique δ (ht.trans ht'.symm) with ⟨rfl, rfl, rfl⟩
  exact hs.symm.trans hs'

theorem no_step_from_halt (δ : Q → A → Q × A × Move)
    (q : Q) (hq : q ∈ H) (h : Move) (L R : Stack (Symbol Q A H)) :
    ¬ ∃ d, Step δ (.main q h, L, R) d := by
  rintro ⟨d, r, L', R', hs, ht⟩
  cases r with
  | main q' h' a =>
    have he : Control.main (q' : Q) h' = Control.main q h := congrArg Prod.fst hs
    have e : (q' : Q) = q := (Control.main.inj he).1
    exact q'.property (e.symm ▸ hq)
  | rightRecord q' g => simp [source] at hs
  | rightWork q' a => simp [source] at hs
  | leftRecord q' g => simp [source] at hs
  | leftWork q' a => simp [source] at hs
end Interspersed
end PrefixFlows
end

end OAI
