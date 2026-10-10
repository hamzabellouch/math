import Mathlib

namespace OAI

universe u

namespace SourceBurnside

structure Root (n : ℕ) where
  row : Fin n
  col : Fin n
  ne : row ≠ col
  deriving DecidableEq

abbrev Generator (n : ℕ) (R : Type u) := Root n × R

def bracket {G : Type u} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

def letter {n : ℕ} {R : Type u} (p : Root n) (a : R) :
    FreeGroup (Generator n R) := FreeGroup.of (p, a)

inductive SteinbergRel (n : ℕ) (R : Type u) [Ring R] :
    FreeGroup (Generator n R) → Prop
  | add (p : Root n) (a b : R) :
      SteinbergRel n R (letter p (a + b) * (letter p a * letter p b)⁻¹)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col) (a b : R) :
      SteinbergRel n R (bracket (letter p a) (letter q b))
  | mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      SteinbergRel n R
        (bracket (letter ⟨i, j, hij⟩ a) (letter ⟨j, k, hjk⟩ b) *
          (letter ⟨i, k, hik⟩ (a * b))⁻¹)

def Steinberg (n : ℕ) (R : Type u) [Ring R] :=
  PresentedGroup {r | SteinbergRel n R r}
  deriving Group

def Periodic (G : Type u) [Group G] : Prop := ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1

def MainStatement : Prop :=
  ∃ (R : Type) (_ : Ring R) (_ : Algebra (ZMod 2) R),
    Infinite (Steinberg 12 R) ∧ Group.IsFinitelyPresented (Steinberg 12 R) ∧
      Periodic (Steinberg 12 R)

def BurnsideStatement : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.IsFinitelyPresented G ∧ Periodic G

end SourceBurnside

namespace SourceBurnside

theorem thm_main : MainStatement ∧ BurnsideStatement := by
  sorry

end SourceBurnside

end OAI
