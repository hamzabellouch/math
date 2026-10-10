import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes

namespace OAI

/-! # Converting height-ball boxes to fixed logarithmic coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set
open scoped Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
theorem exists_height_ball_coordinate_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type*} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H)) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (β : M.Bases) (v : cartanRootIdeal H),
        ‖b.equivFun v‖ ≤ D * Real.exp (B * ρ) *
          ‖(M.boxBasis T hunimod eW ({0} + closedBall 0 ρ) β 1).equivFun v‖ := by
  obtain ⟨β₀, hβ₀, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ {0}
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant M.letter M.wordList b₀
  obtain ⟨B, hB, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  let bZ := M.boxBasis T hunimod eW {0} β₀ 1
  let f := (b.equivFun.toLinearMap.comp bZ.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hf (v : cartanRootIdeal H) : ‖b.equivFun v‖ ≤ ‖f‖ * ‖bZ.equivFun v‖ := by
    simpa only [f, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      f.le_opNorm (bZ.equivFun v)
  refine ⟨‖f‖ * D, B, mul_nonneg (norm_nonneg _) hD, hB, ?_⟩
  intro ρ hρ β v
  have hc := hcompare (M.boxCost T hunimod eW {0})
    (M.boxCost T hunimod eW ({0} + closedBall 0 ρ)) β₀ β hβ₀
    (r := 1) (ε := B * ρ) zero_le_one
    (hcost isCompact_singleton (singleton_nonempty (0 : W)) hρ) v
  change ‖bZ.equivFun v‖ ≤ D * Real.exp (B * ρ * 1) * _ at hc
  simp only [mul_one] at hc
  calc
    _ ≤ ‖f‖ * ‖bZ.equivFun v‖ := hf v
    _ ≤ ‖f‖ * (D * Real.exp (B * ρ) * _) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = _ := by dsimp [boxBasis]; ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
