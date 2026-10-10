import OAI.Analysis.KadisonKastler.RegularTensorGap
import OAI.Analysis.KadisonKastler.GraphRowApproximation

namespace OAI

/-! # Complete linear approximation controls the actual regular tensor gap -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem rescale_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Y : E) {γ : ℝ} (hγ : 0 ≤ γ) (hY : ‖Y‖ ≤ 1 + γ) :
    ‖(((1 + γ)⁻¹ : ℝ) : ℂ) • Y‖ ≤ 1 ∧ ‖Y - (((1 + γ)⁻¹ : ℝ) : ℂ) • Y‖ ≤ γ := by
  have hp : 0 < 1 + γ := by linarith
  have hr : 0 ≤ (1 + γ)⁻¹ := inv_nonneg.mpr hp.le
  have hr1 : (1 + γ)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
  have hn : ‖(((1 + γ)⁻¹ : ℝ) : ℂ)‖ = (1 + γ)⁻¹ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  constructor
  · rw [norm_smul, hn]
    exact (mul_le_mul_of_nonneg_left hY hr).trans_eq (inv_mul_cancel₀ hp.ne')
  · have hid : Y - (((1 + γ)⁻¹ : ℝ) : ℂ) • Y = ((1 - (1 + γ)⁻¹ : ℝ) : ℂ) • Y := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
    calc
      _ ≤ (1 - (1 + γ)⁻¹) * (1 + γ) :=
        mul_le_mul_of_nonneg_left hY (sub_nonneg.mpr hr1)
      _ = γ := by rw [sub_mul, one_mul, inv_mul_cancel₀ hp.ne']; ring

local instance completeMapTensorOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeMapTensorStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeMapTensorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance completeMapTensorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Normalizing the output of a completely close linear map costs at most
one further copy of its error. No positivity assumption is required. -/
theorem matrix_approx_of_completely_close_map
    (M N : VonNeumannAlgebra H) (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) {γ : ℝ} (hγ : 0 ≤ γ)
    (hclose : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M) (hXn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ 2 * γ := by
  let X₀ : CStarMatrix (Fin n) (Fin n) (Algebra M) := fun i j => ⟨X i j, hX i j⟩
  let Y₀ := CStarMatrix.mapₗ F X₀
  have hi : CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toAlgHom.toLinearMap X₀ = X := by
    ext i j
    rfl
  have hn : ‖X₀‖ = ‖X‖ := by
    simpa only [hi] using (injective_starAlgHom_matrix_norm M.toStarSubalgebra.subtype
      Subtype.val_injective X₀).symm
  have hd : ‖X - Y₀‖ ≤ γ := by
    have h := hclose n n X₀
    rw [matrix_map_sub, hi, hn] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hXn hγ).trans_eq (mul_one γ))
  have hY : ‖Y₀‖ ≤ 1 + γ := by
    have h := norm_sub_le_norm_sub_add_norm_sub Y₀ X 0
    simp only [sub_zero, norm_sub_rev] at h
    linarith
  let Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) := (((1 + γ)⁻¹ : ℝ) : ℂ) • Y₀
  obtain ⟨hYn, hYd⟩ := rescale_contraction Y₀ hγ hY
  refine ⟨Y, ?_, hYn, ?_⟩
  · intro i j
    exact N.toStarSubalgebra.smul_mem (hFN (X₀ i j)) _
  · exact (norm_sub_le_norm_sub_add_norm_sub X Y₀ Y).trans
      ((add_le_add hd hYd).trans_eq (by ring))

theorem kkDistance_regularTensorAlgebra_le_of_completely_close_maps
    (M N : VonNeumannAlgebra H)
    (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H)) (G : Algebra N →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) (hGM : ∀ x, G x ∈ M) {γ : ℝ} (hγ : 0 ≤ γ)
    (hF : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (hG : CompletelyBoundedBy (N.toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ 2 * γ :=
  kkDistance_regularTensorAlgebra_le_of_matrix_approx M N (by positivity)
    (matrix_approx_of_completely_close_map M N F hFN hγ hF)
    (matrix_approx_of_completely_close_map N M G hGM hγ hG)

end

end KadisonKastler

end OAI
