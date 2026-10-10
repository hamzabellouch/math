import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]

@[ext] structure Cylinder (Ω : ι → Type*) where
  value : ∀ p, Option (Ω p)

instance : Fintype (Cylinder Ω) := by
  classical
  exact Fintype.ofInjective Cylinder.value (fun _ _ h => Cylinder.ext h)

instance : PartialOrder (Cylinder Ω) where
  le c d := ∀ p a, c.value p = some a → d.value p = some a
  le_refl c := fun _ _ h => h
  le_trans c d e hcd hde := fun p a h => hde p a (hcd p a h)
  le_antisymm c d hcd hdc := by
    apply Cylinder.ext
    funext p
    cases hc : c.value p with
    | none =>
      cases hd : d.value p with
      | none => rfl
      | some a => have := hdc p a hd; simp [hc] at this
    | some a => exact (hcd p a hc).symm

instance : OrderBot (Cylinder Ω) where
  bot := ⟨fun _ => none⟩
  bot_le c := fun p a h => by cases h

namespace Cylinder

def support (c : Cylinder Ω) : Finset ι := by
  classical
  exact Finset.univ.filter (fun p => (c.value p).isSome)

def Holds (c : Cylinder Ω) (x : ∀ p, Ω p) : Prop :=
  ∀ p a, c.value p = some a → x p = a

def Generates (A : Finset (Cylinder Ω)) (c : Cylinder Ω) : Prop :=
  (∀ e ∈ A, e ≤ c) ∧ ∀ p ∈ c.support, ∃ e ∈ A, p ∈ e.support

def Private (A : Finset (Cylinder Ω)) : Prop :=
  ∀ e ∈ A, ∃ p ∈ e.support, ∀ f ∈ A, p ∈ f.support → f = e

def rank (E : Finset (Cylinder Ω)) (c : Cylinder Ω) : ℕ := by
  classical
  exact (E.powerset.filter (fun A => (∀ e ∈ A, e ≤ c) ∧ Private A)).sup Finset.card

end Cylinder

def Intersection (E : Finset (Cylinder Ω)) :=
  {c : Cylinder Ω // ∃ A ⊆ E, Cylinder.Generates A c}

instance (E : Finset (Cylinder Ω)) : Fintype (Intersection E) := by
  classical
  unfold Intersection
  infer_instance

instance (E : Finset (Cylinder Ω)) : PartialOrder (Intersection E) :=
  inferInstanceAs (PartialOrder {c : Cylinder Ω // ∃ A ⊆ E, Cylinder.Generates A c})

instance (E : Finset (Cylinder Ω)) : OrderBot (Intersection E) where
  bot := ⟨⊥, ∅, Finset.empty_subset E, by
    simp [Cylinder.Generates, Cylinder.support]
    intro p
    rfl⟩
  bot_le c := (show (⊥ : Cylinder Ω) ≤ c.val from bot_le)

local instance (E : Finset (Cylinder Ω)) : DecidableEq (Intersection E) := Classical.decEq _
local instance (E : Finset (Cylinder Ω)) : DecidableLE (Intersection E) := Classical.decRel _
local instance (E : Finset (Cylinder Ω)) : DecidableLT (Intersection E) := Classical.decRel _
local instance (E : Finset (Cylinder Ω)) : LocallyFiniteOrder (Intersection E) :=
  Fintype.toLocallyFiniteOrder

def coefficient (E : Finset (Cylinder Ω)) (I : Intersection E) : ℤ :=
  IncidenceAlgebra.mu ℤ (⊥ : Intersection E) I

def retained (E : Finset (Cylinder Ω)) (t : ℕ) : Finset (Intersection E) := by
  classical
  exact Finset.univ.filter (fun I => Cylinder.rank E I.val < t)

def witnesses (E : Finset (Cylinder Ω)) (t : ℕ) : Finset (Intersection E) := by
  classical
  exact Finset.univ.filter (fun I => t ≤ Cylinder.rank E I.val ∧
    ∃ A ⊆ E, A.card ≤ t ∧ Cylinder.Generates A I.val)

def avoidance (E : Finset (Cylinder Ω)) (x : ∀ p, Ω p) : ℤ := by
  classical
  exact if ∀ e ∈ E, ¬e.Holds x then 1 else 0

def truncated (E : Finset (Cylinder Ω)) (t : ℕ) (x : ∀ p, Ω p) : ℤ := by
  classical
  exact ∑ I ∈ retained E t, if I.val.Holds x then coefficient E I else 0

def witnessCount (E : Finset (Cylinder Ω)) (t : ℕ) (x : ∀ p, Ω p) : ℕ := by
  classical
  exact ((witnesses E t).filter (fun I => I.val.Holds x)).card

end OrdinaryCorrelations.SourceCylinder

end

end OAI
