import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicSampling
import OAI.NumberTheory.TwoPoint.Circuits.CircuitProbabilisticMethod
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Independent repetition amplifies the single-hit experiment. These finite
identities are the random-subset step of the circuit polynomial construction. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def isolatesOne {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : Prop :=
  ∃ i ∈ S, ∀ j ∈ S, x j = singleBitPattern i j

lemma singleHitScore_eq_indicator {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    singleHitScore S x = if isolatesOne S x then 1 else 0 := by
  by_cases hx : isolatesOne S x
  · rw [ite_eq_left hx]
    obtain ⟨i, hi, hxi⟩ := hx
    unfold singleHitScore
    rw [sum_eq_single i]
    · exact ite_eq_left hxi
    · intro j hj hji
      unfold cubePattern
      apply ite_eq_right
      intro hxj
      have hh := (hxi i hi).symm.trans (hxj i hi)
      simp [singleBitPattern, Ne.symm hji] at hh
    · exact fun h => (h hi).elim
  · rw [ite_eq_right hx]
    unfold singleHitScore
    apply sum_eq_zero
    intro i hi
    unfold cubePattern
    exact ite_eq_right (fun h => hx ⟨i, hi, h⟩)

theorem bernoulliCubeLaw_isolatesOne (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) :
    (bernoulliCubeLaw n p hp hp1).probability (isolatesOne S) =
      (S.card : ℝ) * p * (1 - p) ^ (S.card - 1) := by
  unfold FiniteLaw.probability
  have heq : (fun x => if isolatesOne S x then (1 : ℝ) else 0) = singleHitScore S :=
    funext (fun x => (singleHitScore_eq_indicator S x).symm)
  rw [heq]
  exact bernoulliCubeLaw_singleHitScore n p hp hp1 S

lemma FiniteLaw.probability_complement {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  unfold FiniteLaw.probability FiniteLaw.average
  calc
    _ = ∑ x, (μ.weight x - μ.weight x * (if E x then (1 : ℝ) else 0)) := by
      apply sum_congr rfl
      intro x _
      by_cases hx : E x <;> simp [hx]
    _ = _ := by rw [sum_sub_distrib, μ.total]

theorem FiniteLaw.independent_failure {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (s : ℕ) :
    (FiniteLaw.independent (fun _ : Fin s => μ)).probability
      (fun x => ∀ i, ¬E (x i)) = (1 - μ.probability E) ^ s := by
  calc
    _ = ∏ _i : Fin s, μ.probability (fun x => ¬E x) :=
      FiniteLaw.independent_probability_all (fun _ : Fin s => μ) (fun _ x => ¬E x)
    _ = _ := by
      simp only [μ.probability_complement, prod_const, card_univ, Fintype.card_fin]

theorem FiniteLaw.independent_failure_le {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (s : ℕ)
    (hE : (1 / 8 : ℝ) ≤ μ.probability E) :
    (FiniteLaw.independent (fun _ : Fin s => μ)).probability
      (fun x => ∀ i, ¬E (x i)) ≤ (7 / 8 : ℝ) ^ s := by
  rw [μ.independent_failure]
  apply pow_le_pow_left₀
  · linarith [μ.probability_le_one E]
  · linarith

end TwoPointCorrelations

end OAI
