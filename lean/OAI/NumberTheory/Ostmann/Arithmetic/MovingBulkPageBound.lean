import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotFieldBridge
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSpectatorPageBound
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkHaarDensity

namespace OAI

/-! # Combining the actual transfer conjugations with the bulk Page density -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem bulk_prime_density_norm {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (δ : ℝ)
    (hlocal : ∀ i, ‖(Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ z, G i z‖ ≤ δ) :
    ‖∑ z, (F (bulkResidueEquiv r p hc z).1 *
        ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)) *
      ∏ j, (selectedPrimeLogDensity P Q (∏ i, bulkResidueModuli r p i)
        (z j).val.val (y j) : ℂ)‖ ≤
      ‖bulkFrequencyPageMean P Q r y F‖ * δ ^ Fintype.card I * ∏ j, ‖(y j : ℂ)⁻¹‖ := by
  have he := bulk_prime_density_crt r p hc P Q hpage y F G
  refine (congrArg norm he).trans_le ?_
  rw [norm_mul, norm_mul]
  simp only [norm_prod]
  change (‖bulkFrequencyPageMean P Q r y F‖ * _) * _ ≤ _
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun j _ => norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∏ _i : I, δ := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hlocal i)
    _ = δ ^ Fintype.card I := by simp only [Finset.prod_const, Finset.card_univ]

/-- The conjugations proved for the original moving slot diagrams give the
required quartet conjugations without any further combinatorial hypothesis. -/
theorem normalized_transfer_bulk_mean {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2))
    (hd : d₁.conjugations = transferConjugations (n + 2) false)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      ∑ z, d₁.bulkValue (normalizedResidueTransform S) z *
        conj (d₂.bulkValue (normalizedResidueTransform S) (z ∘ e.symm))‖ ≤ δ := by
  let c := treeLeafTupleEquiv Bool n (transferConjugations n false)
  have hconj (j : TreeLeafIndex n) :
      quartetBlockEquiv Bool n d₁.conjugations j =
        ((c j, !(c j)), ((!(c j)), !(!(c j)))) := by
    rw [hd]
    simpa only [Bool.not_not] using transferConjugations_quartet n false j
  exact normalized_bulk_spectator_mean_le hp n m hm e hgood S hlo hhi hS hSp
    β ε hε hε1 hprincipal hβ hbias d₁ d₂ c (fun j => !(c j)) hconj δ hδ hnum

end Ostmann

end OAI
