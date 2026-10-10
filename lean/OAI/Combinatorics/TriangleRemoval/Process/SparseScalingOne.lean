import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma sparse_scaling_ge_one (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ) * p ^ 2) (v e : ℕ) (he : e ≤ 2 * v) :
    1 ≤ (n : ℝ) ^ v * p ^ e := by
  calc
    1 ≤ ((n : ℝ) * p ^ 2) ^ v := one_le_pow₀ hD
    _ = (n : ℝ) ^ v * p ^ (2 * v) := by rw [mul_pow,pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp hp1 he) (by positivity)

theorem largeTemplateEligible_of_sparse {k n : ℕ} (T : RootedTemplate k)
    (hroots : T.roots = ∅) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (hs : ∀ W : Finset (Fin k), (T.edges.filter (· ⊆ W)).card ≤ 2 * W.card) :
    largeTemplateEligible T n p := by
  intro W _ F hF hFW
  have hsub : F ⊆ T.edges.filter (· ⊆ W) := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hF he,hFW e he⟩
  have hcount := (Finset.card_le_card hsub).trans (hs W)
  simpa only [hroots,Finset.card_empty,Nat.sub_zero] using
    sparse_scaling_ge_one n p hp hp1 hD W.card F.card hcount

theorem smallTemplateEligible_of_sparse {k n : ℕ} (T : RootedTemplate k) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (htotal : (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card ≤ 1)
    (hs : ∀ J : Finset (Fin k), T.roots ⊆ J → J ≠ Finset.univ →
      (T.edges.filter (· ⊆ J)).card ≤ 2 * (J.card - T.roots.card)) :
    smallTemplateEligible T n p := by
  intro J hJ
  by_cases hfull : J = Finset.univ
  · subst J
    simp only [Finset.subset_univ,Finset.filter_true,Finset.card_univ,Fintype.card_fin,
      Nat.sub_self,pow_zero,mul_one,le_refl]
  · have hI : T.roots.card ≤ J.card := Finset.card_le_card hJ
    have hJk : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
    have hE : (T.edges.filter (· ⊆ J)).card ≤ T.edges.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hden := sparse_scaling_ge_one n p hp hp1 hD
      (J.card - T.roots.card) (T.edges.filter (· ⊆ J)).card (hs J hJ hfull)
    have hid :
        ((n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card)) *
          ((n : ℝ) ^ (J.card - T.roots.card) * p ^ (T.edges.filter (· ⊆ J)).card) =
        (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card := by
      rw [mul_mul_mul_comm,← pow_add,← pow_add]
      congr 2 <;> omega
    have hnon : 0 ≤ (n : ℝ) ^ (k - J.card) *
        p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card) := by positivity
    calc
      _ ≤ ((n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card)) *
          ((n : ℝ) ^ (J.card - T.roots.card) * p ^ (T.edges.filter (· ⊆ J)).card) :=
        le_mul_of_one_le_right hnon hden
      _ = _ := hid
      _ ≤ 1 := htotal

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
