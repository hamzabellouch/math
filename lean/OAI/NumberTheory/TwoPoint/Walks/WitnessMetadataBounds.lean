import OAI.NumberTheory.TwoPoint.Bounds.SingletonFamily
import OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding

namespace OAI

/-! The finite metadata universe yields the actual union bound for singleton systems. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

private lemma nonnegative_cover_sum {A I : Type*} [Fintype A] [Fintype I]
    (weight : A → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (E : A → Prop) (F : I → A → Prop) (hcover : ∀ x, E x → ∃ i, F i x) :
    (∑ x, if E x then weight x else 0) ≤
      ∑ i, ∑ x, if F i x then weight x else 0 := by
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases hx : E x
  · obtain ⟨i, hi⟩ := hcover x hx
    simp only [hx, ite_true]
    have hs := single_le_sum (f := fun i => if F i x then weight x else 0)
      (fun j _ => by split_ifs; exact hw x; exact le_rfl) (mem_univ i)
    simpa only [hi, ite_true] using hs
  · simp only [hx, ite_false]
    exact sum_nonneg (fun i _ => by split_ifs; exact hw x; exact le_rfl)

/-- Count every bounded mode/label/endpoint record and impose only those
support conditions needed for successive elimination. Thus this bound
contains no assumed probability estimate or assumed number of systems. -/
theorem witness_metadata_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n N K h : ℕ) (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ x : ι → P, if ∃ d : WitnessSystemData n N ι,
      K ≤ d.chosen.card ∧ d.Triangular main word h ∧
        d.Holds main word h (integerPrimeAssignment Subtype.val x)
      then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let D := {d : WitnessSystemData n N ι // K ≤ d.chosen.card ∧ d.Triangular main word h}
  let system (d : D) : OrderedPrimeSystem ι := d.val.toSystem main word h d.property.2
  have hcover (x : ι → P)
      (hx : ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
        d.Holds main word h (integerPrimeAssignment Subtype.val x)) :
      ∃ d : D, (system d).Holds (integerPrimeAssignment Subtype.val x) := by
    obtain ⟨d, hd, ht, hh⟩ := hx
    exact ⟨⟨d, hd, ht⟩, hh⟩
  have hu := nonnegative_cover_sum (fun x : ι → P => ∏ z, ((x z).val : ℝ)⁻¹)
    (fun _ => by positivity) _
    (fun d : D => fun x : ι → P => (system d).Holds (integerPrimeAssignment Subtype.val x)) hcover
  have hs := singleton_family_bound system K
    (fun d => by simpa only [system, WitnessSystemData.toSystem_size] using d.property.1)
    P hP hV H B hH hB hlo hhi hdelta (fun _ => 1) (fun _ => by positivity)
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at hs
  refine le_trans ?_ (hs.trans ?_)
  · convert hu using 1
    apply sum_congr rfl
    intro x _
    split_ifs <;> rfl
  · have hc : Fintype.card D ≤ Fintype.card (WitnessSystemData n N ι) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg (by linarith) _))
      (by positivity)

end TwoPointCorrelations

end OAI
