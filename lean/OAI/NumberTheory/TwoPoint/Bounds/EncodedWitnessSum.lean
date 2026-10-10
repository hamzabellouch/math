import OAI.NumberTheory.TwoPoint.Bounds.CodedWitnessFiber
import OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding

namespace OAI

/-! Sum the numerical singleton-witness event over the complete prime-slot catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- The main path and all attached witnesses are segments of one recorded word. -/
def PrimeWordEncoding.Witnesses {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q) (n mainLength : ℕ) (start len : Fin n → ℕ)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) : Prop :=
  e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
    NumericalWitnessEvent (e.decode.take mainLength)
      (fun i => (e.decode.drop (start i)).take (len i))
      (fun z => (e.2.2.1 z).val) h s J supply

theorem encoded_witness_sum_le (R T n K M mainLength h s J : ℕ)
    (start len : Fin n → ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (hRM : R ≤ M) (hsize : 8 * K ≤ n)
    (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ e : PrimeWordEncoding R T P Q,
      if e.Witnesses n mainLength start len h s J supply then e.weight else 0) ≤
      (∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
        (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
          primeHarmonicMass P ^ Fintype.card c.tupleClasses *
          primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  have hP0 : 0 ≤ primeHarmonicMass P := by unfold primeHarmonicMass; positivity
  have hQ0 : 0 ≤ primeHarmonicMass Q := by unfold primeHarmonicMass; positivity
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  rw [Fintype.sum_sigma, sum_mul]
  apply sum_le_sum
  intro t _
  rw [Fintype.sum_sigma, sum_mul]
  apply sum_le_sum
  intro c _
  rw [Fintype.sum_prod_type]
  by_cases hc : c.KindConsistent
  · by_cases hi : c.RowInjective
    · rw [sum_comm]
      let E (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) : Prop :=
        (show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
          n mainLength start len h s J supply
      have hb := c.witness_fiber_reciprocal_bound hc hi hRM mainLength start len P Q E
        (fun a b he => he.2.2) hsize hP hV H B hH hB hlo hhi hdelta
      have heq : (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
          ∑ a : c.tupleClasses → P,
            if (show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
                n mainLength start len h s J supply
              then PrimeWordEncoding.weight ⟨t, c, a, b⟩ else 0) =
          ∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
            ∑ a : c.tupleClasses → P, if E a b then
              (∏ i, ((a i).val : ℝ)⁻¹) * ∏ j, ((b j).val : ℝ)⁻¹ else 0 := by
        apply sum_congr rfl
        intro b _
        apply sum_congr rfl
        intro a _
        dsimp only [E, PrimeWordEncoding.weight]
        rw [reciprocal_product_join]
      rw [heq]
      exact hb
    · have he (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
          ¬(show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
            n mainLength start len h s J supply := fun he => hi he.2.1
      simp only [he, ite_false, sum_const_zero]
      positivity
  · have he (a : c.tupleClasses → P)
        (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
        ¬(show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
          n mainLength start len h s J supply := fun he => hc he.1
    simp only [he, ite_false, sum_const_zero]
    positivity

end TwoPointCorrelations

end OAI
