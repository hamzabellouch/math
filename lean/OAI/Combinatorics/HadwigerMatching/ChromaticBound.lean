import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-! A chromatic lower bound for finite graphs with independence number at most two. -/

namespace HadwigerMatching

open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every color fiber is an independent vertex set, so a coloring by `k`
colors can cover at most `2*k` vertices under the stated independence bound. -/
theorem card_le_twice_of_coloring {k : ℕ} (C : G.Coloring (Fin k))
    (hα : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ 2) :
    Fintype.card V ≤ 2 * k := by
  classical
  let fiber : Fin k → Finset V := fun c => Finset.univ.filter (fun v => C v = c)
  have hfiber (c : Fin k) : (fiber c).card ≤ 2 := by
    apply hα
    intro v hv w hw _ hadj
    exact C.valid hadj ((Finset.mem_filter.mp hv).2.trans
      (Finset.mem_filter.mp hw).2.symm)
  have hcount : ∑ c : Fin k, (fiber c).card = Fintype.card V := by
    simp only [fiber, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  calc
    Fintype.card V = ∑ c : Fin k, (fiber c).card := hcount.symm
    _ ≤ ∑ _c : Fin k, 2 := Finset.sum_le_sum (fun c _ => hfiber c)
    _ = 2 * k := by simp [Nat.mul_comm]

/-- A finite graph has finite chromatic number; an optimal coloring
then proves the lower bound, including the empty vertex type. -/
theorem card_le_twice_chromaticNumber
    (hα : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat := by
  have hfinite : G.chromaticNumber ≠ ⊤ := by
    intro htop
    have h := G.chromaticNumber_le_card
    rw [htop] at h
    simp at h
  obtain ⟨C⟩ := G.colorable_of_chromaticNumber_ne_top hfinite
  exact card_le_twice_of_coloring G C hα

/-- A graph with independence number at most two needs at least half as many
colors as vertices. -/
theorem card_le_twice_chromaticNumber_of_indepNum (hα : G.indepNum ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat := by
  apply card_le_twice_chromaticNumber G
  intro S hS
  exact hS.card_le_indepNum.trans hα

end HadwigerMatching

end OAI
