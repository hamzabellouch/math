import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeStatisticBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedSymmetrizedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateEnumeration

namespace OAI

/-! # The prime statistic for the actual data-dependent template leaf -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplatePrimeStatistic
    (P : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (H : ℝ) (u v a b : ℝ) : ℂ :=
  primeExternalAverage ν (V n) u v a b (fun s y x z =>
    ((movingGiantPhase Subtype.val outside (movingTemplateSmall n r m)
        (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable s y x z *
      movingExternalRegularFactor Subtype.val outside (movingTemplateSmall n r m)
        (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg s y x z) *
      movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) *
      giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)

/-- The exterior factor agrees with the literal template multiplier wherever
its bulk-symmetrized coefficient is nonzero. -/
theorem movingTemplatePrimeStatistic_energy_integrand
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (H : ℝ) (s : ℤ)
    (y : MovingRegularSlot n r m → P) (x z : ℝ) :
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      ((giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) *
        (‖movingExternalRegularFactor Subtype.val outside (movingTemplateSmall n r m)
          (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg s y x z‖ ^ 2 : ℝ)) =
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m (fun _ => true) outside greg s φ H H false y x z := by
  by_cases hc : movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ = 0
  · simp only [hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0), Complex.ofReal_zero, zero_mul]
  have hi := movingBulkAveragedTemplateCoefficient_nonzero_injective Subtype.val
    (fun q : P => hP _ q.property) outside μ childBound pivotBound V F φ G n r m s y
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ hc
  let q := fun i => (y i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (y i).property⟩
  have hprod := movingTemplate_product Subtype.val n r m y
  unfold movingTemplateExternalMultiplier
  dsimp only
  rw [naturalRegularMultiplier_eq_transform_norm]
  simp only [ite_true]
  change _ = _ * (giantOuterWeight _ _ _ _ _ _ *
    (‖movingRegularTransform q (fun i => greg (q i))
      (outside.prod * ⌊Real.exp x⌋₊ * ⌊Real.exp z⌋₊) s‖ ^ 2 : ℝ))
  rw [movingRegularTransform_eq_primeProduct q hi]
  unfold movingExternalRegularFactor
  rw [hprod]

theorem movingTemplatePrimeStatistic_cauchy
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (H u v a b center : ℝ) :
    ‖movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
      greg ggiant favorable H u v a b‖ ^ 2 ≤
    Real.exp (center - u) ^ 2 *
      (mixedExternalAverage ν (V n) u v a b center (fun _ _ x z =>
        giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)).re *
      (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false u v a b center).re := by
  let C := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
    n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let R := movingExternalRegularFactor (Subtype.val : P → ℕ) outside (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg
  let Q := movingGiantPhase (Subtype.val : P → ℕ) outside (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable
  let W := fun x z => giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hsmall : ∀ i ∈ flattenMovingSlots n (movingTemplateSmall n r m),
      i ∉ Set.range (movingTemplateBulk n r m) := movingTemplateSmall_not_bulk n r m
  have hR (e s y x z) : R s (selectedBulkSample (movingTemplateBulk n r m) e y) x z = R s y x z := by
    dsimp only [R, movingExternalRegularFactor]
    rw [MovingSlotReversal.naturalProduct_selected_bulk Subtype.val n m
      (movingTemplateSmall n r m) (movingTemplateBulk n r m) e y hsmall]
  have hQ (e s y x z) : Q s (selectedBulkSample (movingTemplateBulk n r m) e y) x z = Q s y x z :=
    movingGiantPhase_selectedBulkSample Subtype.val outside n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m) e y hsmall ggiant favorable s x z
  have hQnorm (s y x z) : ‖Q s y x z‖ ≤ 1 :=
    movingGiantPhase_norm_le Subtype.val outside (movingTemplateSmall n r m)
      (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable s y x z
  have hW (x z : ℝ) : 0 ≤ (W x z).re ∧ ((W x z).re : ℂ) = W x z := by
    obtain ⟨c, hc, he⟩ := giantOuterWeight_positive φ hφ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W x z = (c : ℂ) at he
    rw [he]
    exact ⟨hc, rfl⟩
  have hc := primeExternalAverage_bounded_statistic_cauchy n m (movingTemplateBulk n r m)
    ν hν hidentical (V n) u v a b center C R Q hR hQ hQnorm
    (fun x z => (W x z).re) (fun x z => (hW x z).1)
  simp only [(hW _ _).2] at hc
  have he : (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (‖mixedBulkSymmetrize n m (movingTemplateBulk n r m) C s y x z‖ ^ 2 : ℂ) *
        (W x z * (‖R s y x z‖ ^ 2 : ℝ)))) =
      movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false u v a b center := by
    unfold movingTemplateMaskedSymmetrizedEnergy
    congr 1
    funext s y x z
    exact movingTemplatePrimeStatistic_energy_integrand P hP outside μ childBound pivotBound V F
      φ G n r m greg H s y x z
  rw [he] at hc
  exact hc

end Ostmann

end OAI
