import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Fixed larger boxes cover the differences of ordinary chart samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W EN N : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

omit [FiniteDimensional ℝ W] in
include hExp in
theorem exists_ordinary_box_difference_cover
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val → ∀ r : ℝ, 0 ≤ r →
      ∀ x ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1,
      ∀ y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1,
        x⁻¹ * y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r D := by
  obtain ⟨C, _, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let D := max 1 (C * (1 + (2 : ℝ)) ^ M.bound * (1 + (1 : ℝ)) ^ M.bound)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro E β hβ r hr x hx y hy
  have hp := hprod E β hβ r hr 2 1 zero_le_one ![x⁻¹, y] (by
    intro i
    fin_cases i
    · exact M.groupBox_inv_mem T hunimod eW eN Exp hExp E β r 1 hx
    · exact hy)
  have hp' : x⁻¹ * y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
      (C * (1 + (2 : ℝ)) ^ M.bound * (1 + (1 : ℝ)) ^ M.bound) := by
    simpa using hp
  obtain ⟨v, hv, hb⟩ := hp'
  exact ⟨v, hv, hb.trans (le_max_right _ _)⟩

omit [T2Space N] hExp in
/-- Nonnegative support widths imply inclusion in every positive
homothetic enlargement without changing the coordinate radius. -/
theorem groupBox_subset_positive_enlargement
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.Bases) {r δ R : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ) :
    M.groupBox T hunimod eW (Exp ∘ eN) E β r R ⊆
      M.groupBox T hunimod eW (Exp ∘ eN) ((fun w => (1 + δ) • w) '' E) β r R := by
  rintro q ⟨v, hv, hb⟩
  refine ⟨v, hv, le_trans ?_ hb⟩
  have hh := norm_change_exponentialRescaleBasis_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW ((fun w => (1 + δ) • w) '' E) (β.val j))
    (fun j => M.boxCost T hunimod eW E (β.val j)) hr (α := 0) (fun j => by
      rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith)]
      have hp : 0 ≤ M.boxCost T hunimod eW E (β.val j) :=
        (bracketWordExponent_pos _ hweights _).le
      nlinarith [mul_nonneg hδ hp]) v
  simpa only [boxBasis, mul_zero, Real.exp_zero, one_mul] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
