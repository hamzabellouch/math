import OAI.NumberTheory.Ostmann.Arithmetic.BulkAbsoluteIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.RestoredBulkSignedBound
import OAI.NumberTheory.Ostmann.Construction.PrimeRestorationDifference

namespace OAI

/-! # The arithmetic norm estimate under the original deleted prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem original_absolute_bulk_bound {J C : Type*} [Fintype J] [Fintype C]
    (primes : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (hu : ∀ j c, 0 < u j c) (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : J → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ)
    (P : PublishedProgressionInput) (Q : ℕ) (W A : ℝ) (hW : 0 ≤ W) (hA0 : 0 ≤ A)
    (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A)
    (err : (J → C) → (J → (ZMod M)ˣ) → ℝ)
    (herror : ∀ c z,
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure P Q M
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z)
    (H T B : ℝ) (hB : 0 ≤ B) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : J → primes) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    (∀ x : J → primes, ‖a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ))‖ ≤ B) →
    ‖∑ x : J → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0)‖ ≤
      (W * A) * 2 ^ Fintype.card J +
        (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z +
        B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  dsimp only
  intro hmass hZ hlow hnorm
  have hmain := restored_bulk_prime_bound primes M u v hu c₀ hP hsep deleted hdeleted
    K a P Q err herror ((W * A) * 2 ^ Fintype.card J)
    (bulk_absolute_mixture_bound P Q M u v hu _ (fun j => by positivity) hmass K a W A hW hA0 hK hA)
  exact original_bulk_collision_restoration_bound primes _ deleted hP hdeleted H T hZ hlow
    _ B hB hnorm _ hmain

end Ostmann

end OAI
