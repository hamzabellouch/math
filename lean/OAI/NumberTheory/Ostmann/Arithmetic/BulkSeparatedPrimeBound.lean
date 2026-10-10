import OAI.NumberTheory.Ostmann.Arithmetic.RestoredBulkSignedBound

namespace OAI

/-! # The separated signed bound under the restored original prime weights -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_separated_prime_bound {I J C : Type*}
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
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z) :
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : J → primes) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let a := fun z => F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    ‖∑ x : J → primes,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        (a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ)))‖ ≤
      (W * A) * 4 ^ Fintype.card J * δ ^ Fintype.card I +
        (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z := by
  dsimp only
  intro hmass
  apply restored_bulk_prime_bound primes _ u v hu c₀ hP hsep D hD K
    (fun z => F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i))
    input Q err herror ((W * A) * 4 ^ Fintype.card J * δ ^ Fintype.card I)
  exact bulk_separated_kernel_bound r p hc input Q hpage u v hu _
    (fun j => by positivity) hmass K F G W A δ hW hA hδ hK hF hlocal

end Ostmann

end OAI
