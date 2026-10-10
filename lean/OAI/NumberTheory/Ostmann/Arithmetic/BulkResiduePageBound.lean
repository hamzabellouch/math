import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCRT

namespace OAI

/-! # Norm bound after exact bulk CRT separation -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkFrequencyPageMean {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q r : ℕ) [NeZero r]
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) : ℂ :=
  (Fintype.card (J → (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ a, F a * ∏ j, pageGiantWeight P Q r (a j).val.val (y j)

noncomputable def bulkSpectatorMean {J : Type*} [Fintype J]
    (p : ℕ) [NeZero p] (G : (J → (ZMod p)ˣ) → ℂ) : ℂ :=
  (Fintype.card (J → (ZMod p)ˣ) : ℂ)⁻¹ * ∑ b, G b

noncomputable def bulkResiduePageMean {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ) (y : J → ℝ)
    (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) : ℂ :=
  (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℂ)⁻¹ *
    (∑ x, (F (bulkResidueEquiv r p hc x).1 *
      ∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (y j)) *
      ∏ i, G i ((bulkResidueEquiv r p hc x).2 i))

theorem bulk_residue_page_bound {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (δ : ℝ) (hlocal : ∀ i, ‖bulkSpectatorMean (p i) (G i)‖ ≤ δ) :
    ‖bulkResiduePageMean r p hc P Q y F G‖ ≤
      ‖bulkFrequencyPageMean P Q r y F‖ * δ ^ Fintype.card I := by
  have he : (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℂ)⁻¹ *
      (∑ x, (F (bulkResidueEquiv r p hc x).1 *
        ∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (y j)) *
        ∏ i, G i ((bulkResidueEquiv r p hc x).2 i)) =
      bulkFrequencyPageMean P Q r y F * ∏ i, bulkSpectatorMean (p i) (G i) :=
    bulk_residue_page_average r p hc P Q hpage y F G
  have hs : ‖∏ i, bulkSpectatorMean (p i) (G i)‖ ≤ δ ^ Fintype.card I := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : I, δ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hlocal i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  calc
    _ = ‖bulkFrequencyPageMean P Q r y F * ∏ i, bulkSpectatorMean (p i) (G i)‖ := congrArg norm he
    _ = ‖bulkFrequencyPageMean P Q r y F‖ * ‖∏ i, bulkSpectatorMean (p i) (G i)‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (norm_nonneg _)

end Ostmann

end OAI
