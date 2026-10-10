import OAI.NumberTheory.TwoPoint.Walks.WitnessMetadata
import OAI.NumberTheory.TwoPoint.Walks.WitnessMetadataBounds
import OAI.NumberTheory.TwoPoint.Walks.WordResampling

namespace OAI

/-! Actual positive minimal witnesses enter the fixed symbolic metadata union. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- Conditions on an actual numerical assignment, before enlarging its event
into the finite union of symbolic relation systems. -/
def ResampledWitnessEvent {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ) (value : ι → ℕ) : Prop :=
  Function.Injective value ∧
  (∀ j, (value j).Prime) ∧
  (∀ i, MinimalWord (ForwardProhibited h s supply) ((word i).resample value).word) ∧
  (∀ i t, t ∈ ((word i).resample value).word → Squarefree t.tuple) ∧
  (∀ i t, t ∈ ((word i).resample value).word → t.tuple.primeFactors.card = J) ∧
  (∀ i p j, TuplePrimeAt ((word i).resample value).word p j →
    ¬p ∣ h ∧ ∀ t ∈ ((word i).resample value).word, ¬p ∣ t.padding) ∧
  (∀ i, value (mark i) ∈ wordPrimeSupport ((word i).resample value).word) ∧
  (∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport ((word j).resample value).word) ∧
  (∀ i v, TuplePrimeAt (main.resample value).word (value (mark i)) v → v = position i) ∧
  ∃ x : ℤ, ∀ i, PositiveWord h
    (x + wordDisplacement h ((main.resample value).word.take (attachment i)))
    ((word i).resample value).word

lemma resampled_witness_metadata {n K h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n) (horder : Monotone attachment)
    (hbound : ∀ i, attachment i ≤ main.word.length)
    (hmainLength : main.word.length ≤ N) (hwordLength : ∀ i, (word i).word.length ≤ N)
    (value : ι → ℕ) (hevent : ResampledWitnessEvent main word h s J supply mark attachment position value) :
    ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  rcases hevent with ⟨hinj, hprime, hminimal, hsq, hcard, hsupport, hmark, hprivate, hmain, x, hpositive⟩
  obtain ⟨d, hd, ht, hh⟩ := witness_system_metadata
    (main.resample value) (fun i => (word i).resample value) value hinj hprime
    (main.resample_realizes value) (fun i => (word i).resample_realizes value)
    mark attachment position hsize hminimal hsq hcard hsupport hmark hprivate horder
    (by simpa only [LabeledPrimeWord.resample_length] using hbound) hmain
    (by simpa only [LabeledPrimeWord.resample_length] using hmainLength)
    (by simpa only [LabeledPrimeWord.resample_length] using hwordLength) x hpositive
  exact ⟨d, hd,
    (d.triangular_pattern (main.resamplePattern value) (fun i => (word i).resamplePattern value) h).mp ht,
    (d.holds_pattern (main.resamplePattern value) (fun i => (word i).resamplePattern value) h _).mp hh⟩

/-- The actual witness event has the same prime-power saving as the metadata
union. Coincident prime assignments are allowed in the enlarged union. -/
theorem resampled_witness_reciprocal_bound {n K h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n) (horder : Monotone attachment)
    (hbound : ∀ i, attachment i ≤ main.word.length)
    (hmainLength : main.word.length ≤ N) (hwordLength : ∀ i, (word i).word.length ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ a : ι → P, if ResampledWitnessEvent main word h s J supply mark attachment position
      (fun z => (a z).val) then ∏ z, ((a z).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  apply le_trans _ (witness_metadata_reciprocal_bound n N K h main word P hP hV H B hH hB hlo hhi hdelta)
  apply sum_le_sum
  intro a _
  by_cases he : ResampledWitnessEvent main word h s J supply mark attachment position (fun z => (a z).val)
  · have hd := resampled_witness_metadata main word mark attachment position hsize horder hbound
      hmainLength hwordLength (fun z => (a z).val) he
    have hd' : ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
        d.Holds main word h (integerPrimeAssignment Subtype.val a) := hd
    rw [ite_eq_left he, ite_eq_left hd']
  · simp only [he, ite_false]
    split_ifs <;> positivity

end TwoPointCorrelations

end OAI
