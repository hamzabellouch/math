import OAI.Combinatorics.ContingencyTables.Transport.LabelledFactorial
import OAI.Combinatorics.ContingencyTables.Transport.BalancedBox

namespace OAI

/-!
# Actual fixed-total signatures give the labelled factorial properties

Every subset count is in its true label-capacity box and its total is the
subset's cardinality. These identities connect the proved integer slice
signatures to the first factorial lift, without any binary-signature input.
-/

namespace ContingencyTables.SliceFactorial

open scoped BigOperators Classical Matrix Topology
open CommonBasesFPRAS BinaryContraction FactorialSignatures LabelledFactorial BalancedBox

variable {L C : Type*} [Fintype L] [Fintype C]

omit [Fintype C] in
lemma groupCount_inBox (group : L → C) (S : Set L) :
    InBox (groupCount group Set.univ) (groupCount group S) := by
  intro c
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_univ] at hi ⊢
  exact hi.2

/-- Positivity of the proved actual total-slice marginal gives positivity
of the literal labelled factorial lift on exactly that subset degree. -/
theorem firstLift_degreePositive (group : L → C) (h : (C → ℕ) → ℝ) (D : ℝ) (R : ℕ)
    (hD : 0 < D) (hpos : PositiveSlice h (groupCount group Set.univ) R) :
    DegreePositive (firstLift group h D) R := by
  intro S hS
  apply div_pos _ hD
  apply mul_pos _ (factorialProduct_positive _)
  apply hpos _ (groupCount_inBox group S)
  rw [groupCount_total,hS]

/-- The exact box-valid raw removal signature implies the omission
property of the manuscript's first lift at its original degree. -/
theorem firstLift_omission_slice (group : L → C) (h : (C → ℕ) → ℝ) (D : ℝ) (R : ℕ)
    (hD : 0 < D) (hh : ∀ z, 0 ≤ h z)
    (hsig : RemovalSlice h (groupCount group Set.univ) R) :
    OmissionProperty (firstLift group h D) R := by
  apply firstLift_omission group h D R hD hh
  intro A hA
  apply hsig _ (groupCount_inBox group Aᶜ)
  rw [groupCount_total]
  have hc := Set.ncard_add_ncard_compl A
  simp only [Nat.card_eq_fintype_card] at hc
  omega

/-- Pointwise limits of actual integer marginals pass directly to their
literal subset factorial displays. -/
theorem firstLift_tendsto {K : Type*} {l : Filter K}
    (group : L → C) (F : K → (C → ℕ) → ℝ) (h : (C → ℕ) → ℝ) (D : ℝ)
    (hlim : ∀ z, Filter.Tendsto (fun t => F t z) l (nhds (h z))) (S : Set L) :
    Filter.Tendsto (fun t => firstLift group (F t) D S) l (nhds (firstLift group h D S)) :=
  ((hlim (groupCount group S)).mul_const (factorialProduct (groupCount group S))).div_const D

end ContingencyTables.SliceFactorial

end OAI
