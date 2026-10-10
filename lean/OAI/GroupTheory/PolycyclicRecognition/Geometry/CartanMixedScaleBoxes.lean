import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOrdinaryBoxCover
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MixedScaleBasisBound

namespace OAI

/-! # The exact box inclusions needed for adjacent-scale comparisons -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L W N : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (Exp : cartanRootIdeal H → N)

/-- Pointwise comparison of actual exponent widths gives inclusion of
exponential boxes, without an additional geometric assumption. -/
theorem groupBox_subset_of_exponent_le
    (E E' : Set W) (β : M.Bases) (r t R : ℝ)
    (h : ∀ w : M.wordList, r * M.boxCost T hunimod eW E w ≤
      t * M.boxCost T hunimod eW E' w) :
    M.groupBox T hunimod eW Exp E β r R ⊆
      M.groupBox T hunimod eW Exp E' β t R := by
  rintro q ⟨v, hv, hc⟩
  refine ⟨v, hv, le_trans ?_ hc⟩
  exact norm_exponentialRescaleBasis_le_of_exponents_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E' (β.val j))
    (fun j => M.boxCost T hunimod eW E (β.val j)) t r (fun j => h (β.val j)) v

theorem groupBox_mono_scale
    (E : Set W) (β : M.Bases) {r t R : ℝ} (hrt : r ≤ t)
    (hcost : ∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w) :
    M.groupBox T hunimod eW Exp E β r R ⊆
      M.groupBox T hunimod eW Exp E β t R :=
  M.groupBox_subset_of_exponent_le T hunimod eW Exp E E β r t R
    (fun w => mul_le_mul_of_nonneg_right hrt (hcost w))

/-- Every nearby larger scale fits inside the fixed strict enlargement
at the smaller scale. The coordinate radius is unchanged. -/
theorem groupBox_scale_le_enlargement
    [FiniteDimensional ℝ W] {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hcost : ∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w)
    (β : M.Bases) {r t δ R : ℝ} (hδ : 0 ≤ δ) (hrt : t ≤ (1 + δ) * r) :
    M.groupBox T hunimod eW Exp E β t R ⊆
      M.groupBox T hunimod eW Exp ((fun w => (1 + δ) • w) '' E) β r R := by
  apply M.groupBox_subset_of_exponent_le T hunimod eW Exp
  intro w
  rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith)]
  calc
    t * M.boxCost T hunimod eW E w ≤ ((1 + δ) * r) * M.boxCost T hunimod eW E w :=
      mul_le_mul_of_nonneg_right hrt (hcost w)
    _ = r * ((1 + δ) * M.boxCost T hunimod eW E w) := by ring

open scoped Manifold

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

/-- One radius covers the differences of a smaller-scale sample and a
larger-scale sample, uniformly in both scales. -/
theorem exists_mixed_scale_box_difference_cover
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential ExpN)
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      (∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w) →
      ∀ r t : ℝ, 0 ≤ t → r ≤ t →
      ∀ x ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β r 1,
      ∀ y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β t 1,
        x⁻¹ * y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β t D := by
  obtain ⟨D, hD, hc⟩ := M.exists_ordinary_box_difference_cover T hunimod eW eN ExpN hExp dynkin b₀
  refine ⟨D, hD, ?_⟩
  intro E β hβ hcost r t ht hrt x hx y hy
  exact hc E β hβ t ht x
    (M.groupBox_mono_scale T hunimod eW (ExpN ∘ eN) E β hrt hcost hx) y hy

end PolycyclicRecognition.CartanWordModel

end

end OAI
