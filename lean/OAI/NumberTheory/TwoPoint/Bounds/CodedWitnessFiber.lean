import OAI.NumberTheory.TwoPoint.Bounds.NumericalWitnessEvent
import OAI.NumberTheory.TwoPoint.Bounds.SplitWitnessSum

namespace OAI

/-! Actual numerical main/witness segments satisfy the fixed-code reciprocal bound. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem CrudeWordCode.witness_fiber_reciprocal_bound {R N n K M h s J : ℕ}
    {supply : ℕ → ℕ → Prop} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective) (hRM : R ≤ M)
    (mainLength : ℕ) (start len : Fin n → ℕ) (P Q : Finset ℕ)
    (E : (c.tupleClasses → P) → ({z : c.usedClasses // z ∉ c.tupleClasses} → Q) → Prop)
    (hE : ∀ a b, E a b →
      let w := c.numericalWord (joinCoordinates c.tupleClasses
        (fun i => (a i).val) (fun j => (b j).val))
      NumericalWitnessEvent (w.take mainLength)
        (fun i => (w.drop (start i)).take (len i)) (fun i => (a i).val) h s J supply)
    (hsize : 8 * K ≤ n) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
      ∑ a : c.tupleClasses → P, if E a b then
        (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
        primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let main := fun b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q =>
    (c.labeledWord (fun j => (b j).val)).segment 0 mainLength
  let word := fun b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q =>
    fun i => (c.labeledWord (fun j => (b j).val)).segment (start i) (len i)
  have hm (b) : (main b).word.length ≤ M := by
    dsimp [main]
    rw [LabeledPrimeWord.segment_length, c.labeledWord_length]
    omega
  have hw (b) (i) : (word b i).word.length ≤ M := by
    dsimp [word]
    rw [LabeledPrimeWord.segment_length, c.labeledWord_length]
    omega
  apply split_witness_reciprocal_bound (h := h) (s := s) (J := J)
    (supply := supply) P Q main word hsize hm hw E ?_
    hP hV H B hH hB hlo hhi hdelta
  intro a b he
  rw [has_resampled_witnesses_iff]
  dsimp [main, word]
  simp only [c.segment_resample_word hc hi, List.drop_zero]
  exact hE a b he

end TwoPointCorrelations

end OAI
