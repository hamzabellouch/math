import OAI.Combinatorics.SecondNeighborhood.Basic
import Mathlib.Data.Fintype.Prod

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

def Counterexample (r : V → V → Prop) : Prop :=
  ∀ v, (secondNeighbors r v).card < (firstNeighbors r v).card

noncomputable def arcSet (r : V → V → Prop) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => r p.1 p.2

def ArcMinimal (r : V → V → Prop) : Prop :=
  ∀ s : V → V → Prop, IsOriented s → Counterexample s →
    (arcSet r).card ≤ (arcSet s).card

def NonemptyBoundary (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    (image r S \ S).Nonempty

def SubsetDeficit (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    (image r (image r S) \ image r S).card < (image r S \ S).card

def PositiveIndegree (r : V → V → Prop) : Prop :=
  ∀ v, ∃ u, r u v

def StrictSubsetGrowth (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    S.card + (image r (image r S)).card < 2 * (image r S).card

omit [DecidableEq V] in
@[simp] theorem mem_arcSet {r : V → V → Prop} {p : V × V} :
    p ∈ arcSet r ↔ r p.1 p.2 := by
  classical
  simp [arcSet]

omit [DecidableEq V] in
theorem arcSet_mono {r s : V → V → Prop}
    (h : ∀ ⦃u v⦄, r u v → s u v) : arcSet r ⊆ arcSet s := by
  intro p hp
  exact mem_arcSet.mpr (h (mem_arcSet.mp hp))

theorem counterexample_iff_not_conjecture (r : V → V → Prop) :
    Counterexample r ↔ ¬ SecondNeighborhoodConjecture r := by
  classical
  simp only [Counterexample, SecondNeighborhoodConjecture, GoodVertex,
    not_exists, not_le]

theorem Counterexample.first_nonempty {r : V → V → Prop}
    (h : Counterexample r) (v : V) : (firstNeighbors r v).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_le_of_lt (Nat.zero_le _) (h v)

end SeymourSecondNeighborhood

end OAI
