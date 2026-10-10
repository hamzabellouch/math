import Mathlib.Data.Nat.Choose.Bounds
import OAI.NumberTheory.Ostmann.Supply.NonnegativeSparseWeight

namespace OAI

/-! # Uniform pointwise bounds for the truncated sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

 theorem elementaryTruncation_range {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    elementaryTruncation b K = ∑ j ∈ Finset.range (K + 1), elementaryCoefficient b j := by
  let T := Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card ≤ K)
  have hmap : ∀ I ∈ T, I.card ∈ Finset.range (K + 1) := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hI).2)
  have he := Finset.sum_fiberwise_of_maps_to hmap (fun I => ∏ i ∈ I, b i)
  change _ = elementaryTruncation b K at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  unfold elementaryCoefficient
  apply Finset.sum_congr
  · ext I
    simp only [T, Finset.mem_filter]
    have hjK := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    constructor
    · rintro ⟨⟨hp, _⟩, he⟩
      exact ⟨hp, he⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨⟨hp, hjK⟩, rfl⟩
  · intro I hI
    rfl

 theorem elementaryCoefficient_norm_le_choose {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (j : ℕ) :
    ‖elementaryCoefficient b j‖ ≤ n.choose j := by
  unfold elementaryCoefficient
  calc
    _ ≤ ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j),
      ‖∏ i ∈ I, b i‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hb i)
    _ = _ := by rw [← Finset.powersetCard_eq_filter]; simp

 theorem elementaryTruncation_norm_le {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (K : ℕ) :
    ‖elementaryTruncation b K‖ ≤ (K + 1 : ℝ) * (n + 1 : ℝ) ^ K := by
  rw [elementaryTruncation_range]
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), ‖elementaryCoefficient b j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (K + 1), (n + 1 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ (n.choose j : ℝ) := elementaryCoefficient_norm_le_choose b hb j
        _ ≤ (n : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow n j
        _ ≤ (n + 1 : ℝ) ^ j := by gcongr; linarith
        _ ≤ (n + 1 : ℝ) ^ K :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp

 theorem localSparseKernel_norm_le_one {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (x : ZMod p) : ‖localSparseKernel E x‖ ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hc : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    simpa only [Finset.card_univ, ZMod.card] using (Nat.cast_le (α := ℝ)).mpr hh
  apply (sparseAdditiveKernel_norm_le E (17 / 20) (by norm_num) x).trans
  have he : (E.card : ℝ) / p ≤ 1 := (div_le_one hp).mpr hc
  calc
    _ = (17 / 20 : ℝ) * (E.card / p) := by ring
    _ ≤ (17 / 20 : ℝ) * 1 := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 1 := by norm_num

 theorem sparseSubsetWeight_uniform_bound {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    sparseSubsetWeight p S K x ≤ ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (elementaryTruncation_norm_le _ (fun i => localSparseKernel_norm_le_one _ _) K) 2

end Ostmann

end OAI
