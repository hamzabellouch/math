import OAI.NumberTheory.Ostmann.Arithmetic.BulkSignedBoxBound
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueMixtures

namespace OAI

/-! # Integrating a separated kernel over the original bulk cell mixtures -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def BulkIntegrand.constMul {J : Type*}
    (f : BulkIntegrand J) (a : ℂ) : BulkIntegrand J where
  toFun y := a * f y
  measurable := measurable_const.mul f.measurable
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun y => by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hf y) (norm_nonneg a)⟩

theorem bulk_separated_kernel_bound {I J C : Type*} [Fintype I] [Fintype J] [Fintype C]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (u v : J → C → ℝ) (hu : ∀ j c, 0 < u j c)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (hmass : ∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2)
    (K : BulkIntegrand J) (F : (J → (ZMod r)ˣ) → ℂ)
    (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (W A δ : ℝ) (hW : 0 ≤ W) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hK : ∀ y, ‖K y‖ ≤ W) (hF : ∀ a, ‖F a‖ ≤ A)
    (hlocal : ∀ i, ‖(Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ z, G i z‖ ≤ δ) :
    let H := fun z => K.constMul (F (bulkResidueEquiv r p hc z).1 *
      ∏ i, G i ((bulkResidueEquiv r p hc z).2 i))
    ‖∑ z, ∫ y, H z y ∂Measure.pi (fun j => bulkCellMixture (Z j)
      (fun c => primeGiantMeasure P Q (∏ i, bulkResidueModuli r p i)
        (z j).val.val (u j c) (v j c)))‖ ≤
      (W * A) * 4 ^ Fintype.card J * δ ^ Fintype.card I := by
  let H := fun (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) =>
    K.constMul (F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i))
  let μ := fun (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) j c =>
    primeGiantMeasure P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (u j c) (v j c)
  let _ : ∀ z j c, IsFiniteMeasure (μ z j c) := fun z j c =>
    finite_primeGiantMeasure P Q _ _ _ _ (hu j c)
  change ‖∑ z, ∫ y, H z y ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ z j))‖ ≤ _
  rw [bulk_residue_mixture_integral Z hZ μ H]
  apply bulk_signed_box_bound r p hc P Q hpage u v hu Z hZ hmass
    (fun _ y a => K y * F a) G (W * A) δ (mul_nonneg hW hA) hδ
  · intro _ y _ a
    rw [norm_mul]
    exact mul_le_mul (hK y) (hF a) (norm_nonneg _) hW
  · exact hlocal
  · intro _ z y
    change (F _ * ∏ i, G i _) * K y = (K y * F _) * ∏ i, G i _
    ring

end Ostmann

end OAI
