import OAI.Combinatorics.Ryser.Domination.Basic

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

structure DominationTrace (G : Graph V) (pool : V → ι)
    (J : Finset ι) (root : ι) (k : ℕ) where
  x : ℕ → V
  y : ℕ → Finset V
  nonempty : ∀ a, a < k → (y a).Nonempty
  disjoint : ∀ a, a < k → ∀ b, b < k → a ≠ b → Disjoint (y a) (y b)
  realized : ∃ U, IsTransversalOn G pool J U ∧
    ∀ a, a < k → neighborsIn G (x a) U = y a
  minimal : ∀ a, a < k → ∀ U, IsTransversalOn G pool J U →
    (∀ b, b < a → neighborsIn G (x b) U = y b) →
      (y a).card ≤ (neighborsIn G (x a) U).card
  origin : ∀ a, a < k → pool (x a) = root ∨
    ∃ b, b < a ∧ ∃ v ∈ y b, pool (x a) = pool v

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

def verticesX (t : DominationTrace G pool J root k) : Finset V :=
  (Finset.range k).image t.x

def verticesY (t : DominationTrace G pool J root k) : Finset V :=
  (Finset.range k).biUnion t.y

def indices (t : DominationTrace G pool J root k) : Finset ι :=
  insert root (t.verticesY.image pool)

def vertices (t : DominationTrace G pool J root k) : Finset V :=
  t.verticesX ∪ t.verticesY

@[simp] theorem mem_verticesY {t : DominationTrace G pool J root k} {v : V} :
    v ∈ t.verticesY ↔ ∃ a, a < k ∧ v ∈ t.y a := by
  simp [verticesY]

@[simp] theorem mem_verticesX {t : DominationTrace G pool J root k} {v : V} :
    v ∈ t.verticesX ↔ ∃ a, a < k ∧ t.x a = v := by
  simp [verticesX]

def empty (v : V) {U : Finset V} (hU : IsTransversalOn G pool J U) :
    DominationTrace G pool J root 0 where
  x := fun _ => v
  y := fun _ => ∅
  nonempty := by simp
  disjoint := by simp
  realized := ⟨U, hU, by simp⟩
  minimal := by simp
  origin := by simp

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
