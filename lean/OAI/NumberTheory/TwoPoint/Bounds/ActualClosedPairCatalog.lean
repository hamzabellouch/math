import OAI.NumberTheory.TwoPoint.Bounds.ResidueMatrixMoment
import OAI.NumberTheory.TwoPoint.Walks.ClosedTraceSummation
import OAI.NumberTheory.TwoPoint.Bounds.PrimeMatrixResidues
import OAI.NumberTheory.TwoPoint.Bounds.PhysicalPathSupport

namespace OAI

/-! The actual trace catalog retains the numerical masks and allowed pair support. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {D V : Type*} [DecidableEq D] [Fintype D] [Fintype V]

def closedPairNumericalTest (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) {k : ℕ} (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) : Prop :=
  shiftWordEnd (integerShiftNext Q tuple h) x p.1 =
      shiftWordEnd (integerShiftNext Q tuple h) x p.2 ∧
    integerPathMask embed Q tuple h gate x p.1 ≠ 0 ∧
    integerPathMask embed Q tuple h gate x p.2 ≠ 0

noncomputable def actualClosedPairCatalog (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ))
    (k : ℕ) (x : D × ℤ) :
    Finset ((Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) :=
  univ.filter (fun p => closedPairNumericalTest embed Q tuple h gate x p ∧
    ∀ t ∈ integerClosedWordCode Q tuple p, (t.tuple, t.padding) ∈ pairs)

omit [DecidableEq D] [Fintype V] in
theorem actualClosedPairCatalog_sum {h J M B k : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (hsupport : ∀ t n, weight t n ≠ 0 → (t.tuple, t.padding) ∈ data.pairs)
    (x : D × ℤ) :
    (∑ a : Fin k → D × (Q × Bool), ∑ b : Fin k → D × (Q × Bool),
      if closedPairNumericalTest embed Q tuple h gate x (a, b) then
        |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
          (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0) =
      ∑ p ∈ actualClosedPairCatalog embed Q tuple h gate data.pairs k x,
        |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
          (data.residueOrigin r) (integerClosedWordCode Q tuple p))| := by
  simp only [actualClosedPairCatalog, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hv : closedPairNumericalTest embed Q tuple h gate x (a, b)
  · by_cases hp : ∀ t ∈ integerClosedWordCode Q tuple (a, b), (t.tuple, t.padding) ∈ data.pairs
    · rw [ite_eq_left hv, ite_eq_left ⟨hv, hp⟩]
    · have hz (r : ↥(data.P ∪ data.Q) → Fin B) :
          scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)) = 0 := by
        by_contra hne
        exact hp (scalarWalkProduct_pairs h weight data.pairs hsupport _ _ hne)
      simp only [hv, hp, and_false, ite_true, ite_false, hz, FiniteLaw.average_const, abs_zero]
  · simp only [hv, false_and, ite_false]

omit [DecidableEq D] [Fintype V] in
theorem actualClosedPairCatalog_closed {h k : ℕ}
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ)) (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool)))
    (hp : p ∈ actualClosedPairCatalog embed Q tuple h gate pairs k x) :
    wordDisplacement h (integerClosedWordCode Q tuple p) = 0 := by
  exact integer_closed_word_displacement Q tuple h x p.1 p.2 (mem_filter.mp hp).2.1.1

theorem actualClosedPairCatalog_chains {h k : ℕ}
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (hinj : Function.Injective tuple)
    (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ)) (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool)))
    (hp : p ∈ actualClosedPairCatalog embed Q tuple h gate pairs k x) :
    ((integerClosedWordCode Q tuple p).take k).IsChain (fun a b => a.tuple ≠ b.tuple) ∧
      ((integerClosedWordCode Q tuple p).drop k).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have ht := (mem_filter.mp hp).2.1
  have ha := integerPathMask_tuple_chain embed Q tuple hinj h gate x p.1 ht.2.1
  have hb := integerPathMask_tuple_chain embed Q tuple hinj h gate x p.2 ht.2.2
  have hlen : (integerStepWord Q tuple p.1).length = k := by
    simp only [integerStepWord, List.length_map, List.length_ofFn]
  have htake : (integerStepWord Q tuple p.1).take k = integerStepWord Q tuple p.1 := by
    simpa only [hlen] using (List.take_length (l := integerStepWord Q tuple p.1))
  have hdrop : (integerStepWord Q tuple p.1).drop k = [] := by
    simpa only [hlen] using (List.drop_length (l := integerStepWord Q tuple p.1))
  simp only [integerClosedWordCode, List.take_append, List.drop_append, hlen, Nat.sub_self,
    List.take_zero, List.drop_zero, List.append_nil, List.nil_append, htake, hdrop]
  exact ⟨ha, reverseWord_chain hb⟩

end TwoPointCorrelations

end OAI
