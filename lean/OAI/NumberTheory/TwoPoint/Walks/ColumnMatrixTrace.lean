import OAI.NumberTheory.TwoPoint.Bounds.ActualClosedPairCatalog
import OAI.NumberTheory.TwoPoint.Bounds.MaskedClosedWordAverage

namespace OAI

/-! The actual residue-model matrix is bounded by the same literal column
catalog to which the four trace estimates apply. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def actualColumnLabel {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hP : ∀ j, P j ⊆ data.P)
    (w : ColumnPrimeAssignment J R P) (t : Fin R × Fin J) : ↥(data.P ∪ data.Q) :=
  ⟨(w t.2 t.1).val, mem_union_left _ (hP t.2 (w t.2 t.1).property)⟩

theorem columnMatrix_residue_trace_le {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s budget : ℕ) (hk : 0 < 2 * k) (hbudget : 2 * k ≤ budget)
    (embed : V → ((j : Fin J) → P j) × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n, g n ≠ 0)
    (hgdep : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (hallowed : ∀ d q, eligible d q → (d, q) ∈ data.pairs) :
    let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
    let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
    (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
      (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
        (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤
      ∑ i : V, ∑ forward, ∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q tuple h gate data.pairs k (embed i)) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun j => (a.2 j).val)) (actualColumnLabel data hP a.1)
          (data.residueValue (fun n => scalarWalkProduct h
            (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K
              (fun t => extra t.tuple) h) n (columnTupleWord a.1 forward (fun j => (a.2 j).val))))| := by
  dsimp only
  let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
  let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
    L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
  let F (i : V) := actualClosedPairCatalog embed Q tuple h gate data.pairs k (embed i)
  have hbound := physicalResidueMatrix_moment_le data hB embed hinj Q tuple gate weight
    (maskedSignedIntegerWeight_flip Q u eligible g _ L K extra h _) k
    (fun a b t ht n m hnm => primeClosedPair_residue_congr data hB hP hprime hdisjoint
      s Q u eligible g L K extra hsq hpool hgdep hextra a b t ht n m hnm)
  refine hbound.trans_eq ?_
  apply sum_congr rfl
  intro i _
  trans (∑ a : Fin k → ((j : Fin J) → P j) × (Q × Bool),
    ∑ b : Fin k → ((j : Fin J) → P j) × (Q × Bool),
    if closedPairNumericalTest embed Q tuple h gate (embed i) (a, b) then
      |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
        (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0)
  · apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    unfold closedPairNumericalTest
    split_ifs <;> rfl
  rw [actualClosedPairCatalog_sum data hB embed Q tuple gate weight
    (maskedSignedIntegerWeight_pairs Q u eligible g _ L K extra h _ data.pairs hallowed)]
  let term (forward : Fin (2 * k) → Bool)
      (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
      (data.residueOrigin r) (columnTupleWord a.1 forward (fun j => (a.2 j).val)))|
  calc
    _ = ∑ p ∈ F i, term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2 := by
      apply sum_congr rfl
      intro p _
      simp only [term, closedTraceEncoding_word]
      rfl
    _ = ∑ forward, ∑ a ∈ closedTraceFiber Q (F i) forward, term forward a :=
      sum_closedTraceFiber Q hprime hdisjoint (F i) term
    _ = _ := by
      apply sum_congr rfl
      intro forward _
      apply sum_congr rfl
      intro a ha
      obtain ⟨p, hp, hword⟩ := closedTraceFiber_word Q (F i) forward a ha
      have hc : wordDisplacement h (columnTupleWord a.1 forward (fun j => (a.2 j).val)) = 0 := by
        rw [hword]
        exact actualClosedPairCatalog_closed embed Q tuple gate data.pairs (embed i) p hp
      dsimp only [term]
      apply congrArg abs
      exact maskedClosedWord_residue_average data hB a.1 forward (fun j => (a.2 j).val)
        hprime hdisjoint (actualColumnLabel data hP a.1) (fun _ _ => rfl)
        s budget hk hbudget hc Q u eligible g L K extra hg

end TwoPointCorrelations

end OAI
