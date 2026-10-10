import OAI.NumberTheory.TwoPoint.Bounds.ResampledWitnesses

namespace OAI

/-! Witness choices are eliminated by the existing relation metadata union. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- The marked labels and attachment positions may depend on the numerical sample. -/
def HasResampledWitnesses {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) (value : ι → ℕ) : Prop :=
  ∃ (mark : Fin n → ι) (attachment position : Fin n → ℕ),
    Monotone attachment ∧ (∀ i, attachment i ≤ main.word.length) ∧
      ResampledWitnessEvent main word h s J supply mark attachment position value

theorem has_resampled_witnesses_reciprocal_bound {n K h s J N : ℕ}
    {supply : ℕ → ℕ → Prop} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (hsize : 8 * K ≤ n) (hmainLength : main.word.length ≤ N)
    (hwordLength : ∀ i, (word i).word.length ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ a : ι → P, if HasResampledWitnesses main word h s J supply
      (fun z => (a z).val) then ∏ z, ((a z).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  apply le_trans _ (witness_metadata_reciprocal_bound n N K h main word P hP hV
    H B hH hB hlo hhi hdelta)
  apply sum_le_sum
  intro a _
  by_cases he : HasResampledWitnesses main word h s J supply (fun z => (a z).val)
  · obtain ⟨mark, attachment, position, horder, hbound, hevent⟩ := he
    have hd := resampled_witness_metadata main word mark attachment position hsize horder
      hbound hmainLength hwordLength (fun z => (a z).val) hevent
    have hd' : ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧
        d.Triangular main word h ∧ d.Holds main word h (integerPrimeAssignment Subtype.val a) := hd
    simp only [ite_eq_left (show HasResampledWitnesses main word h s J supply
      (fun z => (a z).val) from ⟨mark, attachment, position, horder, hbound, hevent⟩),
      ite_eq_left hd']
    exact le_rfl
  · simp only [he, ite_false]
    split_ifs <;> positivity

end TwoPointCorrelations

end OAI
