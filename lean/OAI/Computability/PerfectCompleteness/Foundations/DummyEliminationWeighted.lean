import Mathlib.Tactic.Positivity
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.DummyElimination.Slice

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

private theorem uniform_probability_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (P x)) =
      (Fintype.card {x // P x} : ℝ) / Fintype.card Ω := by
  calc
    _ = (FiniteDistribution.uniform Ω).expectation (fun x => if P x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x <;> simp [hx]
    _ = (∑ x, if P x then (1 : ℝ) else 0) / Fintype.card Ω :=
      FiniteDistribution.expectation_uniform _
    _ = _ := by simp only [Fintype.card_subtype, Finset.sum_boole]

private theorem expectation_condition {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (hp : 0 < μ.probability event)
    (g : Ω → ℝ) :
    (μ.condition event hp).expectation g =
      μ.expectation (fun x => if event x then g x else 0) / μ.probability event := by
  simp only [FiniteDistribution.expectation, FiniteDistribution.condition,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx, mul_left_comm, mul_comm]

variable {𝕜 H D K R C : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup D] [Module 𝕜 D]
  [AddCommGroup K] [Module 𝕜 K] [AddCommGroup R] [Module 𝕜 R]
  [AddCommGroup C] [Module 𝕜 C]
  [Fintype (H →ₗ[𝕜] K)] [Fintype (D →ₗ[𝕜] K)]
  (S : DummyElimination.Slice 𝕜 H D K R C)

def dummyLikelihood (X : H →ₗ[𝕜] K) : ℝ :=
  (FiniteDistribution.uniform (D →ₗ[𝕜] K)).probability (fun Y => decide (S.IsLift X Y))

def dummyConstant : ℝ :=
  (Fintype.card S.HomogeneousMaps : ℝ) / Fintype.card (D →ₗ[𝕜] K)

omit [Fintype (H →ₗ[𝕜] K)] in
theorem dummyConstant_pos : 0 < S.dummyConstant := by
  let : Nonempty S.HomogeneousMaps := ⟨⟨0, by simp [Homogeneous]⟩⟩
  exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)

omit [Fintype (H →ₗ[𝕜] K)] in
theorem dummyLikelihood_eq_card (X : H →ₗ[𝕜] K) :
    S.dummyLikelihood X =
      (Fintype.card {Y : D →ₗ[𝕜] K // S.IsLift X Y} : ℝ) /
        Fintype.card (D →ₗ[𝕜] K) :=
  uniform_probability_card (S.IsLift X)

omit [Fintype (H →ₗ[𝕜] K)] in
theorem dummyLikelihood_eq (hne : ∃ X Y, S.IsLift X Y) (X : H →ₗ[𝕜] K) :
    S.dummyLikelihood X = if S.Projected X then S.dummyConstant else 0 := by
  by_cases hX : S.Projected X
  · obtain ⟨Y, hY⟩ := (S.exists_lift_iff hne X).mpr hX
    rw [ite_eq_left hX, dummyLikelihood_eq_card,
      Fintype.card_congr (S.fiberEquivHomogeneous hY)]; rfl
  · have hnone : ∀ Y, ¬ S.IsLift X Y := fun Y hY => hX (IsLift.projected S hY)
    rw [ite_eq_right hX]
    simp [dummyLikelihood, FiniteDistribution.probability, hnone]

omit [Fintype (H →ₗ[𝕜] K)] in
theorem dummy_restricted_expectation (hne : ∃ X Y, S.IsLift X Y)
    (X : H →ₗ[𝕜] K) (a : ℝ) :
    (FiniteDistribution.uniform (D →ₗ[𝕜] K)).expectation
        (fun Y => if S.IsLift X Y then a else 0) =
      S.dummyConstant * (if S.Projected X then a else 0) := by
  calc
    _ = a * S.dummyLikelihood X := by
      unfold FiniteDistribution.expectation dummyLikelihood FiniteDistribution.probability
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      by_cases hY : S.IsLift X Y <;> simp [hY, mul_comm]
    _ = S.dummyConstant * (if S.Projected X then a else 0) := by
      rw [dummyLikelihood_eq S hne X]
      by_cases hX : S.Projected X <;> simp [hX, mul_comm]

theorem weighted_restricted_expectation (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K)) (g : (H →ₗ[𝕜] K) → ℝ) :
    (μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).expectation
        (fun p => if S.IsLift p.1 p.2 then g p.1 else 0) =
      S.dummyConstant * μ.expectation (fun X => if S.Projected X then g X else 0) := by
  rw [FiniteDistribution.expectation_product]
  calc
    _ = μ.expectation
        (fun X => S.dummyConstant * (if S.Projected X then g X else 0)) :=
      μ.expectation_congr (fun X => S.dummy_restricted_expectation hne X (g X))
    _ = _ := by
      unfold FiniteDistribution.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      exact mul_left_comm _ _ _

theorem padded_probability (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K)) :
    (μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).probability
        (fun p => decide (S.IsLift p.1 p.2)) =
      S.dummyConstant * μ.probability (fun X => decide (S.Projected X)) := by
  simpa [FiniteDistribution.expectation, FiniteDistribution.probability, mul_ite] using
    S.weighted_restricted_expectation hne μ (fun _ => (1 : ℝ))

theorem padded_probability_pos_iff (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K)) :
    0 < (μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).probability
        (fun p => decide (S.IsLift p.1 p.2)) ↔
      0 < μ.probability (fun X => decide (S.Projected X)) := by
  rw [padded_probability S hne μ]
  exact mul_pos_iff_of_pos_left S.dummyConstant_pos

theorem padded_probability_pos (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K))
    (hpos : 0 < μ.probability (fun X => decide (S.Projected X))) :
    0 < (μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).probability
      (fun p => decide (S.IsLift p.1 p.2)) :=
  (S.padded_probability_pos_iff hne μ).mpr hpos

theorem conditioned_expectation_projected (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K))
    (hpos : 0 < μ.probability (fun X => decide (S.Projected X)))
    (g : (H →ₗ[𝕜] K) → ℝ) :
    ((μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).condition
        (fun p => decide (S.IsLift p.1 p.2)) (S.padded_probability_pos hne μ hpos)).expectation
        (fun p => g p.1) =
      (μ.condition (fun X => decide (S.Projected X)) hpos).expectation g := by
  rw [expectation_condition, expectation_condition]
  simp only [decide_eq_true_eq]
  rw [weighted_restricted_expectation S hne μ g, padded_probability S hne μ]
  exact mul_div_mul_left _ _ (ne_of_gt S.dummyConstant_pos)

theorem conditioned_probability_projected (hne : ∃ X Y, S.IsLift X Y)
    (μ : FiniteDistribution (H →ₗ[𝕜] K))
    (hpos : 0 < μ.probability (fun X => decide (S.Projected X)))
    (event : (H →ₗ[𝕜] K) → Bool) :
    ((μ.product (FiniteDistribution.uniform (D →ₗ[𝕜] K))).condition
        (fun p => decide (S.IsLift p.1 p.2)) (S.padded_probability_pos hne μ hpos)).probability
        (fun p => event p.1) =
      (μ.condition (fun X => decide (S.Projected X)) hpos).probability event := by
  simpa [FiniteDistribution.expectation, FiniteDistribution.probability, mul_ite] using
    S.conditioned_expectation_projected hne μ hpos (fun X => if event X then (1 : ℝ) else 0)

end
end PerfectCompleteness.DummyElimination.Slice

end

end OAI
