import OAI.NumberTheory.TwoPoint.Bounds.ExistentialWitnesses
import OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum

namespace OAI

/-! Integrate padding after the singleton witness relations, with distinct-prime weights. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem split_witness_reciprocal_bound {n K h s J N : ℕ}
    {supply : ℕ → ℕ → Prop} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P Q : Finset ℕ) (main : (κ → Q) → LabeledPrimeWord ι)
    (word : (κ → Q) → Fin n → LabeledPrimeWord ι)
    (hsize : 8 * K ≤ n) (hmain : ∀ b, (main b).word.length ≤ N)
    (hword : ∀ b i, (word b i).word.length ≤ N)
    (E : (ι → P) → (κ → Q) → Prop)
    (hE : ∀ a b, E a b → HasResampledWitnesses (main b) (word b) h s J supply
      (fun z => (a z).val))
    (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ b : κ → Q, ∑ a : ι → P, if E a b then
      (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let C : ℝ := (Fintype.card (WitnessSystemData n N ι) : ℝ) *
    primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K
  have hb (b : κ → Q) : (∑ a : ι → P, if E a b then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤ C := by
    apply le_trans _ (has_resampled_witnesses_reciprocal_bound (h := h) (s := s) (J := J)
      (supply := supply) (main b) (word b)
      hsize (hmain b) (hword b) P hP hV H B hH hB hlo hhi hdelta)
    apply sum_le_sum
    intro a _
    by_cases he : E a b
    · simp only [ite_eq_left he, ite_eq_left (hE a b he)]
      exact le_rfl
    · simp only [he, ite_false]
      split_ifs <;> positivity
  calc
    _ = ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) *
        (∑ a : ι → P, if E a b then ∏ i, ((a i).val : ℝ)⁻¹ else 0) := by
      apply sum_congr rfl
      intro b _
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      split_ifs <;> ring
    _ ≤ ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) * C :=
      sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hb b) (by positivity))
    _ = (∑ b : κ → Q, ∏ j, ((b j).val : ℝ)⁻¹) * C := (sum_mul _ _ _).symm
    _ = _ := by rw [sum_reciprocal_assignments]; dsimp [C]; ring

end TwoPointCorrelations

end OAI
