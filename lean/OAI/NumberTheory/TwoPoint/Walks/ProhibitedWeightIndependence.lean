import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightSupport

namespace OAI

/-! The retained departure weight is independent of tuple-prime residue draws.
Only the padding-prime residues enter its divisibility, density and cutoff data. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma squarefree_divisor_congr (Qp : Finset ℕ) (q : ℕ) (hq : Squarefree q)
    (hpool : q.primeFactors ⊆ Qp) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    (q : ℤ) ∣ n ↔ (q : ℤ) ∣ m := by
  rw [squarefree_divisor_iff q hq n, squarefree_divisor_iff q hq m]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    hnm p (hpool hp)]

lemma paddingDensity_eq_of_prime_residues (Qp Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (n m : ℤ) (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) (hg : g n = g m) :
    paddingDensity Q u eligible g n = paddingDensity Q u eligible g m := by
  unfold paddingDensity
  rw [hg]
  congr 1
  apply sum_congr rfl
  intro q hq
  simp only [squarefree_divisor_congr Qp q (hsq q hq) (hpool q hq) n m hnm]

lemma retainedEdgeDeparture_eq_of_prime_residues (Qp Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (hg : ∀ n m : ℤ, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (t : SignedStep) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    retainedEdgeDeparture Q u eligible g L K extra h t n =
      retainedEdgeDeparture Q u eligible g L K extra h t m := by
  by_cases hq : t.padding ∈ Q
  · have hdiv := squarefree_divisor_congr Qp t.padding (hsq _ hq) (hpool _ hq) n m hnm
    have hshift : ∀ p ∈ Qp, ((n + t.displacement h : ℤ) : ZMod p) =
        ((m + t.displacement h : ℤ) : ZMod p) := by
      intro p hp
      simp only [Int.cast_add, hnm p hp]
    have hkeep (n m : ℤ) (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
        integerEdgeKeep Q u (eligible t) g L K (extra t) n ↔
          integerEdgeKeep Q u (eligible t) g L K (extra t) m := by
      unfold integerEdgeKeep
      rw [paddingDensity_eq_of_prime_residues Qp Q u (eligible t) g hsq hpool n m hnm
        (hg n m hnm), hextra t n m hnm]
    unfold retainedEdgeDeparture
    simp only [hdiv, hkeep n m hnm, hkeep _ _ hshift, hg n m hnm]
  · simp only [retainedEdgeDeparture, hq, false_and, ite_false]

theorem retained_word_eq_of_prime_residues {R : ℕ}
    (Qp Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop) (h : ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (hg : ∀ n m : ℤ, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (step : Fin R → SignedStep) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step) =
      scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) m (List.ofFn step) := by
  rw [scalarWalkProduct_ofFn, scalarWalkProduct_ofFn]
  apply prod_congr rfl
  intro i _
  apply retainedEdgeDeparture_eq_of_prime_residues Qp Q u eligible g L K extra h hsq hpool hg hextra
  intro p hp
  simp only [Int.cast_add, hnm p hp]

theorem lifted_retained_word_independent_tuple {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (step : Fin R → SignedStep)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ p ∈ univ.image label, p.val ∈ data.P)
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image label → x p = y p) :
    data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) x =
    data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) y := by
  apply data.residueValue_independent_tuple label hlabel _ _ x y hxy
  exact retained_word_eq_of_prime_residues data.Q Q u eligible g L K extra h hsq hpool hg hextra step

end TwoPointCorrelations

end OAI
