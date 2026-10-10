import OAI.Analysis.Unitarizability.VectorMean
import OAI.Analysis.Unitarizability.CompactMean

namespace OAI

/-! Contracting averages and sparse splitting for nonamenable groups. -/
noncomputable section
namespace Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem rightRegular_opNorm (g : G) : ‖rightRegular g‖ = 1 := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro ξ
    simp [rightRegular_norm_map]
  · have h := (rightRegular g).le_opNorm (indicatorL2 ({1} : Finset G))
    simpa [rightRegular_norm_map, indicatorL2_norm] using h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem regular_sum_norm_le (S : Finset G) :
    ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) := by
  calc
    ‖∑ g ∈ S, rightRegular g‖ ≤ ∑ g ∈ S, ‖rightRegular g‖ := norm_sum_le _ _
    _ = (S.card : ℝ) := by simp [rightRegular_opNorm]

/-- Contrapositive analytic argument using the invariant-mean definition. -/
theorem amenable_of_all_sum_norm
    (h : ∀ S : Finset G, 1 ∈ S → ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ)) :
    Amenable G := by
  classical
  apply amenable_of_approximate_means
  intro S ε hε
  let T := insert 1 (S.image fun g => g⁻¹)
  have h1 : (1 : G) ∈ T := mem_insert_self _ _
  obtain ⟨ξ, hξ, hinv⟩ := almost_invariant_of_sum_norm T h1 (h T h1)
    (show 0 < ε / 2 by positivity)
  refine ⟨vectorMean ξ, ?_, ?_, vectorMean_positive ξ, ?_⟩
  · simpa [hξ] using vectorMean_opNorm_le ξ
  · rw [vectorMean_one, hξ]
    norm_num
  · intro g hg b
    have hg' : g⁻¹ ∈ T := mem_insert_of_mem (mem_image.mpr ⟨g, hg, rfl⟩)
    have hb := vectorMean_translation_bound ξ hξ g b
    have hi := hinv g⁻¹ hg'
    calc
      ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤ 2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := hb
      _ ≤ 2 * ‖b‖ * (ε / 2) := mul_le_mul_of_nonneg_left hi.le (by positivity)
      _ = ε * ‖b‖ := by ring

/-- Nonamenability provides a strict contraction after normalization. -/
theorem exists_contracting_sum (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) * ρ := by
  classical
  have hex : ∃ S : Finset G, 1 ∈ S ∧ ‖∑ g ∈ S, rightRegular g‖ < (S.card : ℝ) := by
    by_contra hnot
    push Not at hnot
    exact hG (amenable_of_all_sum_norm (fun S h1 => le_antisymm (regular_sum_norm_le S) (hnot S h1)))
  obtain ⟨S, h1, hlt⟩ := hex
  have hd : 0 < S.card := card_pos.mpr ⟨1, h1⟩
  have hd2 : 2 ≤ S.card := by
    by_contra hnot
    have hc : S.card = 1 := by omega
    obtain ⟨g, rfl⟩ := card_eq_one.mp hc
    have hg : g = 1 := by simpa [eq_comm] using h1
    subst g
    simp only [sum_singleton, rightRegular_opNorm, card_singleton, Nat.cast_one, lt_self_iff_false] at hlt
  have hdR : (0 : ℝ) < S.card := by exact_mod_cast hd
  obtain ⟨t, hAt, htd⟩ := exists_between hlt
  have ht : 0 < t := lt_of_le_of_lt (norm_nonneg _) hAt
  refine ⟨S, h1, hd2, t / S.card, div_pos ht hdR, (div_lt_one hdR).mpr htd, ?_⟩
  rw [mul_div_cancel₀ _ hdR.ne']
  exact hAt.le

/-- A contracting average with e ∈ S, d ≥ 2, and 0 < ρ < 1. -/
theorem contracting_average (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        ‖((S.card : ℂ)⁻¹) • (∑ g ∈ S, rightRegular g)‖ ≤ ρ := by
  obtain ⟨S, h1, hd, ρ, hρ, hρ1, hsum⟩ := exists_contracting_sum hG
  refine ⟨S, h1, hd, ρ, hρ, hρ1, ?_⟩
  have hdR : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  rw [norm_smul, norm_inv]
  simp only [Complex.norm_natCast]
  calc
    (S.card : ℝ)⁻¹ * ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ)⁻¹ * ((S.card : ℝ) * ρ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hdR.le)
    _ = ρ := by field_simp

/-- Sparse splitting from nonamenability. A single S and ρ work for every
positive word length; all words remain separate labels, even when their group products agree. -/
theorem sparse_splitting_of_nonamenable (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ ℓ : ℕ, 0 < ℓ → ∃ a : G → Word S ℓ → Bool,
        (∀ x, (rowOnes a x).card ≤ ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊) ∧
        ∀ y, (columnZeros a (wordProduct (fun s : S => (s : G)) ℓ) y).card ≤
          ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊ := by
  classical
  obtain ⟨S, h1, hd, ρ, hρ, hρ1, hsum⟩ := exists_contracting_sum hG
  refine ⟨S, h1, hd, ρ, hρ, hρ1, fun ℓ hℓ => ?_⟩
  have hsum' : ‖∑ g : S, rightRegular (g : G)‖ ≤ (Fintype.card S : ℝ) * ρ := by
    simpa only [Fintype.card_coe, Finset.sum_coe_sort] using hsum
  simpa only [Fintype.card_coe] using
    sparse_mask_for_words (fun s : S => (s : G)) hρ.le hsum' ℓ hℓ

end Dixmier

end

end OAI
