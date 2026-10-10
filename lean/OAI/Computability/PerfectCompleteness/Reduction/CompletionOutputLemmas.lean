import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas

namespace OAI


namespace PerfectCompleteness.CompletionOutput

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open WeightRounding CompletionSoundness CompletionRounding
open CompletionSoundness.LegalProjectionGame

noncomputable section

variable {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
  [∀ x, Fintype (L x)]
  (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)

def family : G.CompletionFamily legalL legalR :=
  Classical.choose (G.exists_completionFamily_bounded legalL legalR hsmall (by simp))

theorem family_size (e : Fin m) :
    (family G legalL legalR hsmall).size e ≤
      max 1 (2 * q - Fintype.card (L (G.left e))) := by
  simpa only [family, Fintype.card_fin] using
    Classical.choose_spec
      (G.exists_completionFamily_bounded legalL legalR hsmall (by simp)) e

theorem family_total_size (hq : 0 < q) :
    (∑ e, (family G legalL legalR hsmall).size e) ≤ m * (2 * q) := by
  calc
    _ ≤ ∑ _e : Fin m, 2 * q := by
      apply Finset.sum_le_sum
      intro e _
      exact (family_size G legalL legalR hsmall e).trans
        (max_le (by omega) (Nat.sub_le _ _))
    _ = m * (2 * q) := by simp

def construct (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) : Instance q :=
  CompletionRounding.output w (family G legalL legalR hsmall) δ hδ

@[simp] theorem construct_leftVertices (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) :
    (construct G legalL legalR hsmall w δ hδ).leftVertices = l := rfl

@[simp] theorem construct_rightVertices (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) :
    (construct G legalL legalR hsmall w δ hδ).rightVertices = r := rfl

theorem construct_edge_count (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ)
    (hq : 0 < q) :
    (construct G legalL legalR hsmall w δ hδ).edges.length ≤
      ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q) := by
  exact (output_edge_count_le w (family G legalL legalR hsmall) δ hδ).trans
    (by simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left ⌈(3 : ℚ) / δ⌉₊ (family_total_size G legalL legalR hsmall hq))

theorem construct_word_count (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ)
    (hq : 0 < q) :
    (Encoding.gameWords (construct G legalL legalR hsmall w δ hδ)).length ≤
      4 + (⌈(3 : ℚ) / δ⌉₊ * m * (2 * q)) * (2 * q + 2) := by
  rw [Encoding.gameWords_length]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (2 * q + 2) (construct_edge_count G legalL legalR hsmall w δ hδ hq)) 4

variable [∀ y, Fintype (R y)] [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]

theorem construct_value_le (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) :
    (construct G legalL legalR hsmall w δ hδ).value ≤
      G.value + G.occurrences.expectation
        (fun e => 2 / (2 * q - Fintype.card (L (G.left e)) : Nat)) + (δ : ℝ) / 3 :=
  output_value_le w (family G legalL legalR hsmall) hweights δ hδ hq

theorem construct_value_le_of_residual_bound (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (η : ℝ)
    (hη : ∀ e, 2 / (2 * q - Fintype.card (L (G.left e)) : Nat) ≤ η) :
    (construct G legalL legalR hsmall w δ hδ).value ≤ G.value + η + (δ : ℝ) / 3 :=
  output_value_le_of_residual_bound w (family G legalL legalR hsmall) hweights δ hδ hq η hη

theorem construct_perfectlyComplete (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (hcomplete : G.value = 1) :
    PerfectlyComplete (construct G legalL legalR hsmall w δ hδ) := by
  apply ((construct G legalL legalR hsmall w δ hδ).perfectlyComplete_iff_value_eq_one hq).2
  exact output_value_eq_one w (family G legalL legalR hsmall) hweights δ hδ hq hcomplete

theorem construct_soundAt (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (η : ℝ)
    (hη : ∀ e, 2 / (2 * q - Fintype.card (L (G.left e)) : Nat) ≤ η)
    (d : RationalThreshold)
    (hbudget : G.value + η + (δ : ℝ) / 3 ≤ (d.numerator : ℝ) / d.denominator) :
    SoundAt d (construct G legalL legalR hsmall w δ hδ) := by
  apply ((construct G legalL legalR hsmall w δ hδ).soundAt_iff_value_le hq d).2
  exact (construct_value_le_of_residual_bound G legalL legalR hsmall w hweights
    δ hδ hq η hη).trans hbudget

end
end PerfectCompleteness.CompletionOutput


namespace PerfectCompleteness.CompletionParameters

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open WeightRounding CompletionSoundness CompletionOutput

noncomputable section

theorem residual_le_third {q n : Nat} {δ : ℝ} (hq : 0 < q)
    (hn : n ≤ q) (hδ : 0 < δ) (hbudget : 6 ≤ δ * q) :
    2 / (2 * q - n : Nat) ≤ δ / 3 := by
  have hden : q ≤ 2 * q - n := by omega
  have hden_real : (q : ℝ) ≤ (2 * q - n : Nat) := by exact_mod_cast hden
  have hpos : (0 : ℝ) < (2 * q - n : Nat) := by
    exact_mod_cast lt_of_lt_of_le hq hden
  rw [div_le_iff₀ hpos]
  have hmul := mul_le_mul_of_nonneg_left hden_real (le_of_lt hδ)
  nlinarith

def embedFin (T : Type*) [Fintype T] (n : Nat) (h : Fintype.card T ≤ n) : T ↪ Fin n :=
  (Fintype.equivFin T).toEmbedding.trans (Fin.castLEEmb h)

section Game
variable {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
  [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
  (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)

theorem construct_value_le_delta (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q)
    (hleft : ∀ x, Fintype.card (L x) ≤ q)
    (hbudget : (6 : ℝ) ≤ (δ : ℝ) * q)
    (hsound : G.value ≤ (δ : ℝ) / 3) :
    (construct G legalL legalR hsmall w δ hδ).value ≤ (δ : ℝ) := by
  have hδreal : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hres : ∀ e, 2 / (2 * q - Fintype.card (L (G.left e)) : Nat) ≤ (δ : ℝ) / 3 :=
    fun e => residual_le_third hq (hleft (G.left e)) hδreal hbudget
  have h := construct_value_le_of_residual_bound G legalL legalR hsmall
    w hweights δ hδ hq ((δ : ℝ) / 3) hres
  linarith

theorem construct_soundAt_of_budget (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q)
    (hleft : ∀ x, Fintype.card (L x) ≤ q)
    (hbudget : (6 : ℝ) ≤ (δ : ℝ) * q)
    (hsound : G.value ≤ (δ : ℝ) / 3) (d : RationalThreshold)
    (hthreshold : (δ : ℝ) ≤ (d.numerator : ℝ) / d.denominator) :
    SoundAt d (construct G legalL legalR hsmall w δ hδ) := by
  apply ((construct G legalL legalR hsmall w δ hδ).soundAt_iff_value_le hq d).2
  exact (construct_value_le_delta G legalL legalR hsmall w hweights
    δ hδ hq hleft hbudget hsound).trans hthreshold

end Game

theorem exists_target {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
    [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
    [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
    (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
    (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)
    (hleft : ∀ x, Fintype.card (L x) ≤ q)
    (hright : ∀ y, Fintype.card (R y) ≤ q)
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q)
    (hbudget : (6 : ℝ) ≤ (δ : ℝ) * q) :
    ∃ target : Instance q,
      target.leftVertices = l ∧ target.rightVertices = r ∧
      target.edges.length ≤ ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q) ∧
      (G.value = 1 → PerfectlyComplete target) ∧
      (G.value ≤ (δ : ℝ) / 3 → target.value ≤ (δ : ℝ)) := by
  let legalL : ∀ x, L x ↪ Fin (2 * q) :=
    fun x => embedFin (L x) (2 * q) ((hleft x).trans (by omega))
  let legalR : ∀ y, R y ↪ Fin q := fun y => embedFin (R y) q (hright y)
  refine ⟨construct G legalL legalR hsmall w δ hδ, rfl, rfl,
    construct_edge_count G legalL legalR hsmall w δ hδ hq, ?_, ?_⟩
  · exact construct_perfectlyComplete G legalL legalR hsmall w hweights δ hδ hq
  · exact construct_value_le_delta G legalL legalR hsmall w hweights δ hδ hq hleft hbudget

end
end PerfectCompleteness.CompletionParameters

end OAI
