import OAI.Combinatorics.BalancedRyser.Probability.PermutationSubsetLaw
import OAI.Combinatorics.BalancedRyser.Probability.UniformSubsetExposure

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
attribute [local instance] Classical.propDecidable

theorem two_species_subset_uncovered_mean {A B P : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq P]
    (U : Finset A) (V : Finset B) (X : Finset P)
    (incidentA : P → A → Prop) (incidentB : P → B → Prop)
    (d e : ℕ) (hd : d ≤ U.card) (he : e ≤ V.card) :
    (𝔼 S ∈ U.powersetCard d, 𝔼 T ∈ V.powersetCard e,
      ((X.filter (fun p =>
        (∀ l ∈ U \ S, ¬ incidentA p l) ∧
        (∀ l ∈ V \ T, ¬ incidentB p l))).card : ℝ)) =
      ∑ p ∈ X,
        ((d.descFactorial (U.filter (incidentA p)).card : ℝ) /
          (U.card.descFactorial (U.filter (incidentA p)).card : ℝ)) *
        ((e.descFactorial (V.filter (incidentB p)).card : ℝ) /
          (V.card.descFactorial (V.filter (incidentB p)).card : ℝ)) := by
  classical
  rw [← Finset.expect_product']
  rw [Finset.expect_eq_sum_div_card, Finset.sum_div]
  convert (uniform_expected_filtered_card _
    ((Finset.powersetCard_nonempty.mpr hd).product (Finset.powersetCard_nonempty.mpr he))
    X (fun p S => (∀ l ∈ U \ S.1, ¬ incidentA p l) ∧
      (∀ l ∈ V \ S.2, ¬ incidentB p l))).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S hS
    congr 3
    ext p
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro p hp
    simp_rw [uncovered_iff_incident_subset]
    exact uniform_two_subsets_contains_probability U (U.filter (incidentA p))
      V (V.filter (incidentB p)) d e
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd he

theorem permutation_target_uncovered_mean {A B P : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq P]
    (I : Finset A) (J : Finset B) (i x : A) (hi : i ∉ I)
    (X : Finset P) (incidentA : P → A → Prop) (incidentB : P → B → Prop) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm A => σ i = x),
      𝔼 τ : Equiv.Perm B,
        ((X.filter (fun p =>
          (∀ l ∈ (Finset.univ.erase x) \ I.map σ.toEmbedding, ¬ incidentA p l) ∧
          (∀ l ∈ Finset.univ \ J.map τ.toEmbedding, ¬ incidentB p l))).card : ℝ)) =
      ∑ p ∈ X,
        ((I.card.descFactorial ((Finset.univ.erase x).filter (incidentA p)).card : ℝ) /
          ((Finset.univ.erase x).card.descFactorial
            ((Finset.univ.erase x).filter (incidentA p)).card : ℝ)) *
        ((J.card.descFactorial (Finset.univ.filter (incidentB p)).card : ℝ) /
          ((Finset.univ : Finset B).card.descFactorial
            (Finset.univ.filter (incidentB p)).card : ℝ)) := by
  classical
  have hI : I.card ≤ (Finset.univ.erase x).card := by
    have hsub : I ⊆ (Finset.univ.erase i) := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ x)] using Finset.card_le_card hsub
  have hJ : J.card ≤ (Finset.univ : Finset B).card :=
    Finset.card_le_card (Finset.subset_univ J)
  convert (PermutationSubsetLaw.expect_two_images_conditioned_target I J i x hi
    (fun S T => ((X.filter (fun p =>
      (∀ l ∈ (Finset.univ.erase x) \ S, ¬ incidentA p l) ∧
      (∀ l ∈ Finset.univ \ T, ¬ incidentB p l))).card : ℝ))).trans ?_ using 1
  convert two_species_subset_uncovered_mean (Finset.univ.erase x) Finset.univ
      X incidentA incidentB I.card J.card hI hJ using 1
  apply Finset.expect_congr rfl
  intro S hS
  apply Finset.expect_congr rfl
  intro T hT
  congr 2
  ext p
  simp only [Finset.mem_filter]

end Balanced

end OAI
