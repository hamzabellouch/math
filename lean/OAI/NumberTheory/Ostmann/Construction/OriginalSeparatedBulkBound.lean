import OAI.NumberTheory.Ostmann.Arithmetic.BulkSeparatedPrimeBound
import OAI.NumberTheory.Ostmann.Construction.PrimeRestorationDifference
import OAI.NumberTheory.Ostmann.Construction.SignedBulkGain

namespace OAI

/-! # The separated estimate under the original deleted, distinct bulk law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Compose Page replacement, the separated signed estimate, restoration of
omitted primes and collision removal without changing the original normalizers. -/
theorem original_separated_bulk_bound {I J C : Type*}
    [Fintype I] [Fintype J] [Fintype C]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (primes : Finset ℕ) (u v : J → C → ℝ) (hu : ∀ j c, 0 < u j c)
    (c₀ : C × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : C × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : C × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : C × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ D j, (q : ℝ)⁻¹) ≠ 0)
    (K : BulkIntegrand J) (F : (J → (ZMod r)ˣ) → ℂ)
    (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (W A δ : ℝ) (hW : 0 ≤ W) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hK : ∀ y, ‖K y‖ ≤ W) (hF : ∀ a, ‖F a‖ ≤ A)
    (hlocal : ∀ i, ‖(Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ z, G i z‖ ≤ δ)
    (input : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero input Q) =
      pageAtModulus r (selectedPageZero input Q))
    (err : (J → C) → (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) → ℝ)
    (herror : ∀ c z,
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure (∏ i, bulkResidueModuli r p i)
        (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure input Q (∏ i, bulkResidueModuli r p i)
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z)
    (H T B : ℝ) (hB : 0 ≤ B) :
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : J → primes) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let a := fun z => F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ D j → Real.exp T ≤ (q : ℝ)) →
    (∀ x : J → primes, ‖a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ))‖ ≤ B) →
    ‖∑ x : J → primes,
      ((∏ j, primeSubsetPrior primes (S j \ D j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0)‖ ≤
      (W * A) * 4 ^ Fintype.card J * δ ^ Fintype.card I +
        (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z +
        B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) := by
  dsimp only
  intro hmass hZ hlow hnorm
  have hb := bulk_separated_prime_bound r p hc primes u v hu c₀ hP hsep D hD K F G
    W A δ hW hA hδ hK hF hlocal input Q hpage err herror
  dsimp only at hb
  exact original_bulk_collision_restoration_bound primes _ D hP hD H T hZ hlow
    _ B hB hnorm _ (hb hmass)

/-- At the actual tree-and-word cardinalities, the separated main term has
any prescribed fixed exponential saving after the quartet tolerance is chosen. -/
theorem original_bulk_main_gain {n m : ℕ} (C D W A δ E : ℝ)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hAexp : A ≤ Real.exp (C * m)) (hδgain : δ ≤ signedBulkGainTarget n C D)
    (z : ℂ)
    (hz : ‖z‖ ≤ (W * A) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) *
      δ ^ Fintype.card (Fin m) + E) :
    ‖z‖ ≤ W * Real.exp (-D * m) + E := by
  apply hz.trans
  apply add_le_add _ le_rfl
  simpa only [Fintype.card_fin] using signedBulkGainTarget_bound n m C D W A δ hW hA hδ hAexp hδgain

end Ostmann

end OAI
