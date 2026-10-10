import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.AmbientEviction

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma evictionFraction_univ (X : Finset A) : evictionFraction X Finset.univ = 0 := by
  simp [evictionFraction]

omit [Fintype A] in
lemma evictionFraction_inter (X U V : Finset A) :
    evictionFraction X (U ∩ V) ≤ evictionFraction X U + evictionFraction X V := by
  have hsub : X \ (U ∩ V) ⊆ (X \ U) ∪ (X \ V) := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold evictionFraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

omit [Fintype A] in
lemma trim_failure_inter (X U : Finset A)
    (h : ((X ∩ U).card : ℝ) < (9/10:ℝ)*X.card) :
    (1:ℝ)/10 ≤ evictionFraction X U := by
  have hp : (0:ℝ) < X.card := by
    have h0 : (0:ℝ) ≤ (X ∩ U).card := Nat.cast_nonneg _
    linarith only [h, h0]
  have he : X \ (X ∩ U) = X \ U := by ext a; simp
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := X) (s₂ := U))
  rw [he] at hc
  have hc' : ((X \ U).card : ℝ) + (X ∩ U).card = X.card := by exact_mod_cast hc
  exact (le_div_iff₀ hp).mpr (by linarith only [h, hc'])

theorem optional_inter_drift (p : Law Ω) (X U : Finset A)
    (out : Ω → Option (Finset A)) (ρ : ℝ)
    (h : (∑ ω, p ω * evictionFraction X (ReverseCap.ambientTest (out ω))) ≤ ρ) :
    (∑ ω, p ω * ((out ω).map (fun V => U ∩ V)).elim 0 (evictionFraction X)) ≤
      evictionFraction X U + ρ := by
  calc
    _ ≤ ∑ ω, p ω * (evictionFraction X U + evictionFraction X (ReverseCap.ambientTest (out ω))) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
      cases ho : out ω with
      | none => simpa [ReverseCap.ambientTest, evictionFraction_univ] using evictionFraction_nonneg X U
      | some V => simpa [ReverseCap.ambientTest] using evictionFraction_inter X U V
    _ = evictionFraction X U + (∑ ω, p ω * evictionFraction X (ReverseCap.ambientTest (out ω))) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_one, one_mul]
    _ ≤ _ := add_le_add_right h _

lemma optional_constant_drift {M : Ω → Type*} (p : Law Ω) (enc : ∀ ω, Option (M ω))
    (c : ℝ) (hc : 0 ≤ c) :
    (∑ ω, p ω * (enc ω).elim 0 (fun _ => c)) ≤ c := by
  calc
    _ ≤ ∑ ω, p ω * c := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
      cases enc ω <;> simp [hc]
    _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]

omit [Fintype A] in
theorem reached_trim_mass {C : Type*} [Fintype C]
    (p : Law Ω) (ctx : Ω → Option C) (domain : C → Finset A) (X : Finset A)
    (ρ : ℝ) (h : (∑ ω, p ω * (ctx ω).elim 0 (fun c => evictionFraction X (domain c))) ≤ ρ) :
    eventMass p (Finset.univ.filter (fun ω => ∃ c, ctx ω = some c ∧
      ((X ∩ domain c).card : ℝ) < (9/10:ℝ)*X.card)) ≤ 10*ρ := by
  let E := Finset.univ.filter (fun ω => ∃ c, ctx ω = some c ∧
    ((X ∩ domain c).card : ℝ) < (9/10:ℝ)*X.card)
  have hm := event_markov p (fun ω => (ctx ω).elim 0 (fun c => evictionFraction X (domain c)))
    (by intro ω; cases ctx ω with
        | none => exact le_rfl
        | some c => exact evictionFraction_nonneg _ _)
    (1/10) E (by
      intro ω hω
      obtain ⟨c, he, ht⟩ := (Finset.mem_filter.mp hω).2
      simpa [he] using trim_failure_inter X (domain c) ht)
  change eventMass p E ≤ _
  linarith only [hm, h]

end SharpRamseyFive.FiniteEntropy

end OAI
