import OAI.NumberTheory.TwoPoint.Bounds.PaddingActiveState
import OAI.NumberTheory.TwoPoint.Walks.WeightedWordCircuit

namespace OAI

/-! The actual retained departure coefficient is an explicit function
of the finite padding states at its two endpoints. This is the scalar
coefficient used in the signed finite-law expansion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingStateDensity {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : ℕ → Prop) (S : Finset (Fin m)) : ℝ :=
  (∑ q ∈ Q, if eligible q ∧ q.primeFactors ⊆ S.image (fun i => (e i).val)
    then actualPaddingCoefficient q else 0) / (5 : ℝ) ^ S.card

noncomputable def paddingStateKeep {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : ℕ → Prop) (L K : ℝ) (S : Finset (Fin m)) : Prop :=
  paddingStateDensity Qp Q e eligible S ≤ K / L ∧ (S.card : ℝ) ≤ 400 * Real.log L

noncomputable def paddingStateDeparture {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) : ℝ :=
  if t.padding ∈ Q ∧ eligible t t.padding ∧
      t.padding.primeFactors ⊆ S.image (fun i => (e i).val) ∧
      paddingStateKeep Qp Q e (eligible t) L K S ∧
      paddingStateKeep Qp Q e (eligible t) L K T
    then L * actualPaddingCoefficient t.padding / (5 : ℝ) ^ S.card else 0

lemma paddingDensity_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → Prop) (n : ℤ) :
    paddingDensity Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) n =
      paddingStateDensity Qp Q e eligible (paddingActiveState Qp e n) := by
  unfold paddingDensity paddingStateDensity
  rw [actualPaddingVertex_sq_activeState Qp e n]
  congr 1
  apply sum_congr rfl
  intro q hq
  simp only [retainedPadding_dvd_iff_activeState Qp hQp e q (hQ hq) n]

lemma integerEdgeKeep_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → Prop) (L K : ℝ) (n : ℤ) :
    integerEdgeKeep Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
      (actualPaddingDegreeCut Qp L) n ↔
      paddingStateKeep Qp Q e eligible L K (paddingActiveState Qp e n) := by
  simp only [integerEdgeKeep, paddingStateKeep, paddingDensity_eq_state Qp Q hQp hQ e,
    actualPaddingDegreeCut, paddingActiveState_card]

lemma retainedEdgeDeparture_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ)
    (h : ℕ) (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
      (fun _ => actualPaddingDegreeCut Qp L) h t n =
      paddingStateDeparture Qp Q e eligible L K t
        (paddingActiveState Qp e n) (paddingActiveState Qp e (n + t.displacement h)) := by
  unfold retainedEdgeDeparture paddingStateDeparture
  by_cases hq : t.padding ∈ Q
  · simp only [retainedPadding_dvd_iff_activeState Qp hQp e t.padding (hQ hq) n,
      integerEdgeKeep_eq_state Qp Q hQp hQ e,
      actualPaddingVertex_sq_activeState Qp e n]
  · simp only [hq, false_and, ite_false]

lemma paddingStateDeparture_nonneg {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hL : 0 ≤ L) :
    0 ≤ paddingStateDeparture Qp Q e eligible L K t S T := by
  unfold paddingStateDeparture
  split_ifs
  · exact div_nonneg (mul_nonneg hL (actualPaddingCoefficient_nonneg _)) (by positivity)
  · exact le_rfl

lemma paddingStateDeparture_le {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hL : 0 ≤ L) :
    paddingStateDeparture Qp Q e eligible L K t S T ≤ L * actualPaddingCoefficient t.padding := by
  unfold paddingStateDeparture
  split_ifs
  · exact div_le_self (mul_nonneg hL (actualPaddingCoefficient_nonneg _))
      (one_le_pow₀ (by norm_num))
  · exact mul_nonneg hL (actualPaddingCoefficient_nonneg _)

end TwoPointCorrelations

end OAI
