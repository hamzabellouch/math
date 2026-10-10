import OAI.Analysis.KadisonKastler.MatrixCentralResidual
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A fixed contraction gives arbitrary one-vector refinement

The reference vector may move by a summable prescribed amount. Each
step contracts only the residual orthogonal to its current central line;
projection onto the new line can only improve that estimate.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_central_refinement_geometric
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J →
      inner ℂ η (matrixStageCentralProjection E J ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F J η‖ ≤ q * ‖η‖)
    (n : ℕ) (E : FiniteMatrixStage M) (η : H) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ‖matrixCentralResidual F J ξ η‖ ≤ q ^ n * ‖matrixCentralResidual E J ξ η‖ := by
  induction n generalizing E δ with
  | zero => exact ⟨E,le_rfl,by simpa using hδ.le,by simp⟩
  | succ n ih =>
    obtain ⟨F,hEF,hFdisp,hF⟩ := ih E (δ / 2) (half_pos hδ)
    obtain ⟨G,hFG,hGdisp,hG⟩ := hstep F (matrixCentralResidual F J ξ η)
      (matrixCentralResidual_mem F J ξ η) (matrixCentralResidual_orthogonal F J ξ η)
      (δ / 2) (half_pos hδ)
    refine ⟨G,hEF.trans hFG,?_,?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub (matrixStageCentralProjection E J ξ)
        (matrixStageCentralProjection F J ξ) (matrixStageCentralProjection G J ξ)).trans
        ((add_le_add hFdisp hGdisp).trans_eq (add_halves δ))
    · calc
        ‖matrixCentralResidual G J ξ η‖ ≤
            ‖matrixStageCentralProjection G J (matrixCentralResidual F J ξ η)‖ :=
          matrixCentralResidual_refinement_le F G hFG J ξ η
        _ ≤ q * ‖matrixCentralResidual F J ξ η‖ := hG
        _ ≤ q * (q ^ n * ‖matrixCentralResidual E J ξ η‖) :=
          mul_le_mul_of_nonneg_left hF hq
        _ = q ^ (n+1) * ‖matrixCentralResidual E J ξ η‖ := by rw [pow_succ]; ring

theorem exists_central_refinement_of_contraction
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J →
      inner ℂ η (matrixStageCentralProjection E J ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F J η‖ ≤ q * ‖η‖)
    (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
        c • matrixStageCentralProjection F J ξ‖ ≤ ε := by
  have ht : Tendsto (fun n : ℕ => q ^ n * ‖matrixCentralResidual E J ξ η‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖matrixCentralResidual E J ξ η‖
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨F,hEF,hdisp,hres⟩ := exists_central_refinement_geometric J ξ q hq hstep n E η δ hδ
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient F J ξ η
  exact ⟨F,hEF,hdisp,c,by rw [← hc]; exact hres.trans hn.le⟩

end

end KadisonKastler

end OAI
