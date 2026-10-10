import Mathlib.Data.Rat.Cast.Order
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Reduction.TargetGameLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.PerfectCompleteness.Sampling.FiniteListSampling
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.BoundedListSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Index A : Type*} [Fintype A]

def listLaw (L : Finset A) (default : A) : FiniteDistribution A :=
  if h : L.Nonempty then FiniteListSampling.uniformList L h
  else FiniteListSampling.uniformList {default} (Finset.singleton_nonempty default)

theorem listLaw_of_nonempty (L : Finset A) (default : A) (h : L.Nonempty) :
    listLaw L default = FiniteListSampling.uniformList L h := by
  simp [listLaw, h]

@[simp] theorem listLaw_empty_weight (default a : A) :
    (listLaw ∅ default).weight a = if a = default then 1 else 0 := by
  simp [listLaw, FiniteListSampling.uniformList]

theorem listLaw_weight_mem (L : Finset A) (default a : A) (ha : a ∈ L) :
    (listLaw L default).weight a = 1 / (L.card : ℝ) := by
  rw [listLaw_of_nonempty L default ⟨a, ha⟩]
  exact FiniteListSampling.uniformList_weight_mem L ⟨a, ha⟩ a ha

theorem listLaw_weight_lower (L : Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : (L.card : ℝ) ≤ M) (a : A) (ha : a ∈ L) :
    1 / M ≤ (listLaw L default).weight a := by
  rw [listLaw_weight_mem L default a ha]
  have hcardPos : 0 < (L.card : ℝ) := Nat.cast_pos.mpr (Finset.Nonempty.card_pos ⟨a, ha⟩)
  apply (div_le_div_iff₀ hM hcardPos).mpr
  simpa only [one_mul] using hcard

theorem list_success_lower (L : Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : (L.card : ℝ) ≤ M) (event : A → Bool)
    (witness : ∃ a ∈ L, event a = true) :
    1 / M ≤ (listLaw L default).probability event := by
  obtain ⟨a, ha, hevent⟩ := witness
  exact (listLaw_weight_lower L default M hM hcard a ha).trans
    (FiniteListSampling.probability_ge_weight (listLaw L default) event a hevent)

variable [Fintype Index] [Nonempty Index]

def jointLaw (L : Index → Finset A) (default : A) : FiniteDistribution (Index × A) :=
  CleanConditioning.kernelJoint (FiniteDistribution.uniform Index) (fun σ => listLaw (L σ) default)

@[simp] theorem jointLaw_weight (L : Index → Finset A) (default : A) (σ : Index) (a : A) :
    (jointLaw L default).weight (σ, a) =
      (1 / (Fintype.card Index : ℝ)) * (listLaw (L σ) default).weight a := rfl

theorem jointLaw_probability (L : Index → Finset A) (default : A) (event : Index × A → Bool) :
    (jointLaw L default).probability event =
      ∑ σ, (1 / (Fintype.card Index : ℝ)) *
        (listLaw (L σ) default).probability (fun a => event (σ, a)) :=
  CleanConditioning.probability_kernelJoint _ _ _

theorem jointLaw_index_law (L : Index → Finset A) (default : A) :
    (jointLaw L default).pushforward Prod.fst = FiniteDistribution.uniform Index := by
  apply FiniteDistribution.eq_of_weight_eq
  intro σ
  change (∑ p : Index × A, if p.1 = σ then
    (FiniteDistribution.uniform Index).weight p.1 * (listLaw (L p.1) default).weight p.2 else 0) =
      (FiniteDistribution.uniform Index).weight σ
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ τ, if τ = σ then (FiniteDistribution.uniform Index).weight τ else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hτ : τ = σ
      · simp only [ite_eq_left hτ, ← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
      · simp only [ite_eq_right hτ, Finset.sum_const_zero]
    _ = _ := by simp

theorem jointLaw_weight_ge_of_mem (L : Index → Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (σ : Index) (a : A) (ha : a ∈ L σ) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (jointLaw L default).weight (σ, a) := by
  rw [jointLaw_weight, ← one_div_mul_one_div]
  exact mul_le_mul_of_nonneg_left (listLaw_weight_lower (L σ) default M hM (hcard σ) a ha)
    (one_div_nonneg.mpr (Nat.cast_nonneg _))

theorem joint_success_lower (L : Index → Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (event : Index × A → Bool) (witness : ∃ σ a, a ∈ L σ ∧ event (σ, a) = true) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (jointLaw L default).probability event := by
  obtain ⟨σ, a, ha, hevent⟩ := witness
  exact (jointLaw_weight_ge_of_mem L default M hM hcard σ a ha).trans
    (FiniteListSampling.probability_ge_weight (jointLaw L default) event (σ, a) hevent)

theorem joint_success_lower_of_indices (L : Index → Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (event : Index × A → Bool) (good : Index → Bool)
    (witness : ∀ σ, good σ = true → ∃ a ∈ L σ, event (σ, a) = true) :
    (FiniteDistribution.uniform Index).probability good / M ≤
      (jointLaw L default).probability event := by
  have hstep : ∀ σ, (if good σ then 1 / M else 0) ≤
      (listLaw (L σ) default).probability (fun a => event (σ, a)) := by
    intro σ
    by_cases hgood : good σ = true
    · simpa only [hgood, ite_true] using
        list_success_lower (L σ) default M hM (hcard σ) _ (witness σ hgood)
    · simpa [hgood] using
        (listLaw (L σ) default).probability_nonnegative (fun a => event (σ, a))
  calc
    _ = ∑ σ, (FiniteDistribution.uniform Index).weight σ * (if good σ then 1 / M else 0) := by
      simp only [FiniteDistribution.probability, Finset.sum_div, ite_div, zero_div,
        mul_ite, mul_one_div, mul_zero]
    _ ≤ ∑ σ, (FiniteDistribution.uniform Index).weight σ *
        (listLaw (L σ) default).probability (fun a => event (σ, a)) :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hstep σ)
        ((FiniteDistribution.uniform Index).nonnegative σ))
    _ = _ := (jointLaw_probability L default event).symm

def outputLaw {B : Type*} [Fintype B] (L : Index → Finset A) (default : A)
    (decode : Index → A → B) : FiniteDistribution B :=
  (jointLaw L default).pushforward (fun p => decode p.1 p.2)

theorem outputLaw_probability {B : Type*} [Fintype B]
    (L : Index → Finset A) (default : A) (decode : Index → A → B) (event : B → Bool) :
    (outputLaw L default decode).probability event =
      (jointLaw L default).probability (fun p => event (decode p.1 p.2)) :=
  FiniteDistribution.probability_pushforward _ _ _

theorem output_success_lower {B : Type*} [Fintype B]
    (L : Index → Finset A) (default : A) (decode : Index → A → B)
    (M : ℝ) (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (event : B → Bool)
    (witness : ∃ σ a, a ∈ L σ ∧ event (decode σ a) = true) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (outputLaw L default decode).probability event := by
  rw [outputLaw_probability]
  exact joint_success_lower L default M hM hcard _ witness

theorem output_weight_ge_of_mem {B : Type*} [Fintype B]
    (L : Index → Finset A) (default : A) (decode : Index → A → B)
    (M : ℝ) (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (σ : Index) (a : A) (ha : a ∈ L σ) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (outputLaw L default decode).weight (decode σ a) := by
  have h := output_success_lower L default decode M hM hcard
    (fun b => decide (b = decode σ a)) ⟨σ, a, ha, by simp⟩
  simpa [FiniteDistribution.probability] using h

theorem independent_match_lower {B C : Type*} [Fintype B] [Fintype C] [Nonempty C]
    (L : Index → Finset A) (default : A) (decode : Index → A → B)
    (M : ℝ) (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (accepts : C → B → Bool)
    (witness : ∃ σ a, a ∈ L σ ∧ ∃ c, accepts c (decode σ a) = true) :
    1 / ((Fintype.card C : ℝ) * (Fintype.card Index : ℝ) * M) ≤
      ((FiniteDistribution.uniform C).product (outputLaw L default decode)).probability
        (fun p => accepts p.1 p.2) := by
  obtain ⟨σ, a, ha, c, haccept⟩ := witness
  have hright := output_weight_ge_of_mem L default decode M hM hcard σ a ha
  calc
    _ = (1 / (Fintype.card C : ℝ)) * (1 / ((Fintype.card Index : ℝ) * M)) := by
      simp only [one_div_mul_one_div, mul_assoc]
    _ ≤ ((FiniteDistribution.uniform C).product (outputLaw L default decode)).weight
        (c, decode σ a) :=
      mul_le_mul_of_nonneg_left hright ((FiniteDistribution.uniform C).nonnegative c)
    _ ≤ _ := FiniteListSampling.probability_ge_weight _ _ (c, decode σ a) haccept

end
end PerfectCompleteness.BoundedListSampling



namespace PerfectCompleteness.LegalUniform

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open WeightRounding

noncomputable section

def enumeratedWeights {E : Type*} [Fintype E]
    (f : E → ℚ) (hpositive : ∀ e, 0 < f e) (htotal : ∑ e, f e = 1)
    (enum : E ≃ Fin (Fintype.card E)) : PositiveWeights (Fintype.card E) where
  weight i := f (enum.symm i)
  positive i := hpositive (enum.symm i)
  total := (enum.symm.sum_comp f).trans htotal

theorem transport_weight_eq_enumerated {E : Type*} [Fintype E]
    (μ : FiniteDistribution E) (f : E → ℚ)
    (hpositive : ∀ e, 0 < f e) (htotal : ∑ e, f e = 1)
    (hweights : ∀ e, μ.weight e = (f e : ℝ))
    (enum : E ≃ Fin (Fintype.card E)) (i : Fin (Fintype.card E)) :
    (μ.transport enum).weight i =
      ((enumeratedWeights f hpositive htotal enum).weight i : ℝ) :=
  hweights (enum.symm i)

def uniformWeights (E : Type*) [Fintype E] [Nonempty E] :
    PositiveWeights (Fintype.card E) where
  weight _ := 1 / (Fintype.card E : ℚ)
  positive _ := by
    have hcard : (0 : ℚ) < Fintype.card E := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
    exact div_pos zero_lt_one hcard
  total := by
    have hcard : (Fintype.card E : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hcard

@[simp] theorem uniformWeights_weight (E : Type*) [Fintype E] [Nonempty E]
    (i : Fin (Fintype.card E)) :
    (uniformWeights E).weight i = 1 / (Fintype.card E : ℚ) := rfl

theorem transport_uniform_weight {E : Type*} [Fintype E] [Nonempty E]
    (μ : FiniteDistribution E) (huniform : μ = FiniteDistribution.uniform E)
    (enum : E ≃ Fin (Fintype.card E)) (i : Fin (Fintype.card E)) :
    (μ.transport enum).weight i = ((uniformWeights E).weight i : ℝ) := by
  rw [huniform]
  change (1 / (Fintype.card E : ℝ)) = ((1 / (Fintype.card E : ℚ) : ℚ) : ℝ)
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem equivFin_uniform_weight {E : Type*} [Fintype E] [Nonempty E]
    (μ : FiniteDistribution E) (huniform : μ = FiniteDistribution.uniform E)
    (i : Fin (Fintype.card E)) :
    (μ.transport (Fintype.equivFin E)).weight i =
      ((uniformWeights E).weight i : ℝ) :=
  transport_uniform_weight μ huniform (Fintype.equivFin E) i

theorem exists_uniform_weights {E : Type*} [Fintype E] [Nonempty E]
    (μ : FiniteDistribution E) (huniform : μ = FiniteDistribution.uniform E) :
    ∃ w : PositiveWeights (Fintype.card E),
      (∀ i, w.weight i = 1 / (Fintype.card E : ℚ)) ∧
      ∀ i, (μ.transport (Fintype.equivFin E)).weight i = (w.weight i : ℝ) := by
  exact ⟨uniformWeights E, uniformWeights_weight E, equivFin_uniform_weight μ huniform⟩

end
end PerfectCompleteness.LegalUniform

end OAI
