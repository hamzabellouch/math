import OAI.Combinatorics.BalancedRyser.Probability.HypergeometricApproximation

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
attribute [local instance] Classical.propDecidable

theorem uniform_product_event_probability {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (hA : A.Nonempty) (hB : B.Nonempty)
    (P : α → Prop) (Q : β → Prop) :
    ((PMF.uniformOfFinset (A ×ˢ B) (hA.product hB)).toOuterMeasure
      {x | P x.1 ∧ Q x.2}).toReal =
      ((PMF.uniformOfFinset A hA).toOuterMeasure {x | P x}).toReal *
        ((PMF.uniformOfFinset B hB).toOuterMeasure {x | Q x}).toReal := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  have hf : (A ×ˢ B).filter (fun x => P x.1 ∧ Q x.2) = (A.filter P) ×ˢ (B.filter Q) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hf, Finset.card_product, Finset.card_product]
  push_cast
  ring

theorem uniform_two_subsets_contains_probability {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (U T : Finset α) (V R : Finset β) (d e : ℕ)
    (hTU : T ⊆ U) (hRV : R ⊆ V) (hd : d ≤ U.card) (he : e ≤ V.card) :
    ((PMF.uniformOfFinset ((U.powersetCard d) ×ˢ (V.powersetCard e))
      (Finset.Nonempty.product (Finset.powersetCard_nonempty.mpr hd)
        (Finset.powersetCard_nonempty.mpr he))).toOuterMeasure
      {S | T ⊆ S.1 ∧ R ⊆ S.2}).toReal =
      ((d.descFactorial T.card : ℝ) / (U.card.descFactorial T.card : ℝ)) *
        ((e.descFactorial R.card : ℝ) / (V.card.descFactorial R.card : ℝ)) := by
  rw [uniform_product_event_probability _ _ (Finset.powersetCard_nonempty.mpr hd)
    (Finset.powersetCard_nonempty.mpr he)]
  rw [uniform_subset_contains_probability U T d hTU hd,
    uniform_subset_contains_probability V R e hRV he]

theorem uniform_expected_filtered_card {Ω α : Type*} [DecidableEq Ω] [DecidableEq α]
    (A : Finset Ω) (hA : A.Nonempty) (X : Finset α) (P : α → Ω → Prop) :
    (∑ ω ∈ A, ((X.filter (fun x => P x ω)).card : ℝ) / (A.card : ℝ)) =
      ∑ x ∈ X, ((PMF.uniformOfFinset A hA).toOuterMeasure {ω | P x ω}).toReal := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
    Finset.sum_div]
  exact Finset.sum_comm

theorem uncovered_iff_incident_subset {L : Type*} [DecidableEq L]
    (D S : Finset L) (incident : L → Prop) :
    (∀ l ∈ D \ S, ¬ incident l) ↔ D.filter incident ⊆ S := by
  classical
  constructor
  · intro h l hl
    rcases Finset.mem_filter.mp hl with ⟨hlD, hlI⟩
    by_contra hlS
    exact h l (Finset.mem_sdiff.mpr ⟨hlD, hlS⟩) hlI
  · intro h l hl hlI
    rcases Finset.mem_sdiff.mp hl with ⟨hlD, hlS⟩
    exact hlS (h (Finset.mem_filter.mpr ⟨hlD, hlI⟩))

theorem uniform_two_subsets_expected_uncovered_card {L α : Type*}
    [DecidableEq L] [DecidableEq α]
    (D C : Finset L) (X : Finset α) (incident : α → L → Prop)
    (d c : ℕ) (hd : d ≤ D.card) (hc : c ≤ C.card) :
    (∑ S ∈ (D.powersetCard d) ×ˢ (C.powersetCard c),
      ((X.filter (fun x =>
        (∀ l ∈ D \ S.1, ¬ incident x l) ∧ (∀ l ∈ C \ S.2, ¬ incident x l))).card : ℝ) /
          (((D.powersetCard d) ×ˢ (C.powersetCard c)).card : ℝ)) =
      ∑ x ∈ X,
        ((d.descFactorial ((D.filter (incident x)).card) : ℝ) /
          (D.card.descFactorial ((D.filter (incident x)).card) : ℝ)) *
        ((c.descFactorial ((C.filter (incident x)).card) : ℝ) /
          (C.card.descFactorial ((C.filter (incident x)).card) : ℝ)) := by
  classical
  convert (uniform_expected_filtered_card _
    ((Finset.powersetCard_nonempty.mpr hd).product (Finset.powersetCard_nonempty.mpr hc))
    X (fun x S => (∀ l ∈ D \ S.1, ¬ incident x l) ∧ (∀ l ∈ C \ S.2, ¬ incident x l))).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S hS
    congr 1
    congr 2
    ext x
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro x hx
    simp_rw [uncovered_iff_incident_subset]
    exact uniform_two_subsets_contains_probability D (D.filter (incident x))
      C (C.filter (incident x)) d c (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd hc

end Balanced

end OAI
