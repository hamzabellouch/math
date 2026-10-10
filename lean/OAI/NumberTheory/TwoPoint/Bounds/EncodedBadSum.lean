import OAI.NumberTheory.TwoPoint.Walks.ProhibitedPrimeEncoding
import OAI.NumberTheory.TwoPoint.Bounds.BadCatalogCost

namespace OAI

/-! The prohibited-word reciprocal estimate summed over all finite codes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem encoded_prohibited_sum_le (R T h s J : ℕ) (P Q : Finset ℕ)
    (supply : ℕ → ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ e : PrimeWordEncoding R T P Q,
      if e.Prohibited h s J supply then e.weight else 0) ≤
      (∑ n : Fin (T + 1), ∑ c : CrudeWordCode R n.val R,
        c.badReciprocalCost (primeHarmonicMass P) (primeHarmonicMass Q)) *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  rw [Fintype.sum_sigma]
  rw [sum_mul]
  apply sum_le_sum
  intro n _
  rw [Fintype.sum_sigma]
  rw [sum_mul]
  apply sum_le_sum
  intro c _
  rw [Fintype.sum_prod_type]
  by_cases hc : c.KindConsistent
  · by_cases hi : c.RowInjective
    · rw [sum_comm]
      let E (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) : Prop :=
        PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply
      have hE : ∀ a b, E a b →
          let w := c.numericalWord (joinCoordinates c.tupleClasses
            (fun z => (a z).val) (fun z => (b z).val))
          Function.Injective (fun z => (a z).val) ∧
          ForwardProhibited h s supply w ∧
          (∀ t ∈ w, Squarefree t.tuple) ∧
          (∀ t ∈ w, t.tuple.primeFactors.card = J) ∧
          (∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ t ∈ w, ¬p ∣ t.padding) := by
        intro a b he
        exact he.2.2
      have hb := c.prohibited_fiber_reciprocal_bound hc hi P Q E hE
        hP hVP H B hH hB hlo hhi
      have heq : (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
          ∑ a : c.tupleClasses → P,
            if PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply
              then PrimeWordEncoding.weight ⟨n, c, a, b⟩ else 0) =
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
          ¬PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply := fun he => hi he.2.1
      simp only [he, ite_false, sum_const_zero]
      exact mul_nonneg (c.badReciprocalCost_nonneg
        (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
        (by positivity)
  · have he (a : c.tupleClasses → P)
        (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
        ¬PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply := fun he => hc he.1
    simp only [he, ite_false, sum_const_zero]
    exact mul_nonneg (c.badReciprocalCost_nonneg
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
      (by positivity)

/-- Length and slot-count summation retain the one-prime saving. -/
theorem bounded_encoded_prohibited_sum_le (T h s J : ℕ) (P Q : Finset ℕ)
    (supply : ℕ → ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ R : Fin (s + 1), ∑ e : PrimeWordEncoding R.val T P Q,
      if e.Prohibited h s J supply then e.weight else 0) ≤
      badCatalogCost s T (primeHarmonicMass P) (primeHarmonicMass Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  unfold badCatalogCost
  rw [sum_mul]
  exact sum_le_sum (fun R _ => encoded_prohibited_sum_le R.val T h s J P Q supply
    hP hVP H B hH hB hlo hhi)

end TwoPointCorrelations

end OAI
