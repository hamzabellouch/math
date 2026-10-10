import OAI.NumberTheory.Ostmann.Arithmetic.BulkSignedIntegralBound
import OAI.NumberTheory.Ostmann.Arithmetic.BulkBoxReassembly
import OAI.NumberTheory.Ostmann.Construction.HarmonicBoxMass

namespace OAI

/-! # Reassembling the signed bulk integral over all original cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Summing all boxes with their original harmonic normalization costs only
an exponential in the number of slots. The spectator gain is retained. -/
theorem bulk_signed_box_bound {I J C : Type*} [Fintype I] [Fintype J] [Fintype C]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (u v : J → C → ℝ) (hu : ∀ j c, 0 < u j c)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (hmass : ∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2)
    (F : (J → C) → (J → ℝ) → (J → (ZMod r)ˣ) → ℂ)
    (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hF : ∀ c y, (∀ j, y j ∈ Set.Ioc (u j (c j)) (v j (c j))) → ∀ a, ‖F c y a‖ ≤ A)
    (hlocal : ∀ i, ‖(Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ z, G i z‖ ≤ δ)
    (f : (J → C) → (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) → BulkIntegrand J)
    (hf : ∀ c z y, f c z y = F c y (bulkResidueEquiv r p hc z).1 *
      ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z, ∫ y, f c z y ∂Measure.pi (fun j =>
      primeGiantMeasure P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (u j (c j)) (v j (c j)))‖ ≤
      A * 4 ^ Fintype.card J * δ ^ Fintype.card I := by
  let H := fun j c => ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹
  have hH (j : J) (c : C) : 0 ≤ H j c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.mpr ((hu j c).trans hx.1).le
  let E := fun c : J → C => ∑ z, ∫ y, f c z y ∂Measure.pi (fun j =>
    primeGiantMeasure P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (u j (c j)) (v j (c j)))
  have hE (c : J → C) : ‖E c‖ ≤ ((A * 2 ^ Fintype.card J) * δ ^ Fintype.card I) *
      ∏ j, H j (c j) :=
    bulk_signed_integral_bound r p hc P Q hpage (fun j => u j (c j)) (fun j => v j (c j))
      (fun j => hu j (c j)) (F c) G A δ hA hδ (hF c) hlocal (f c) (hf c)
  have h := bulk_box_sum_bound Z hZ H hH hmass ((A * 2 ^ Fintype.card J) * δ ^ Fintype.card I)
    (mul_nonneg (mul_nonneg hA (by positivity)) (pow_nonneg hδ _)) E hE
  refine h.trans_eq ?_
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  ring

end Ostmann

end OAI
