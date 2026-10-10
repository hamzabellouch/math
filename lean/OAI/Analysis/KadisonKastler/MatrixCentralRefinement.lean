import OAI.Analysis.KadisonKastler.CentralLineApproximation

namespace OAI

/-! # Passing central-vector refinement estimates to finite families

Further matrix refinement preserves every previous distance-to-line
estimate. Repeated one-vector refinement therefore handles any finite
family with a prescribed total displacement budget.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixStageCentralProjection (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) : H →L[ℂ] H :=
  (centralVectorSpace (matrixUnitConcreteAlgebra E.units) J).starProjection

theorem matrixStageCentralProjection_error_mono (E F : FiniteMatrixStage M)
    (hEF : E.units.concreteAlgebra ≤ F.units.concreteAlgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (c : ℂ) :
    ‖matrixStageCentralProjection F J η - c • matrixStageCentralProjection F J ξ‖ ≤
      ‖matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ‖ := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra F.units) J
  have hcomp : K.starProjection ∘L matrixStageCentralProjection E J = K.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (centralVectorSpace_antitone hEF J)
  have he (x : H) : K.starProjection (matrixStageCentralProjection E J x) =
      matrixStageCentralProjection F J x :=
    congrArg (fun T : H →L[ℂ] H => T x) hcomp
  calc
    _ = ‖K.starProjection (matrixStageCentralProjection E J η -
        c • matrixStageCentralProjection E J ξ)‖ := by rw [map_sub,map_smul,he,he]
    _ ≤ _ := K.norm_starProjection_apply_le _

theorem exists_finite_central_refinement
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε)
    (η : ℕ → H) (n : ℕ) (E : FiniteMatrixStage M) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ∀ i < n, ∃ c : ℂ, ‖matrixStageCentralProjection F J (η i) -
        c • matrixStageCentralProjection F J ξ‖ ≤ ε := by
  induction n generalizing E δ with
  | zero => exact ⟨E,le_rfl,by simpa using hδ.le,by simp⟩
  | succ n ih =>
    obtain ⟨F,hEF,hδF,hF⟩ := ih E (δ / 2) (half_pos hδ)
    obtain ⟨G,hFG,hδG,c,hc⟩ := hstep F (η n) (δ / 2) ε (half_pos hδ) hε
    refine ⟨G,hEF.trans hFG,?_,?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub (matrixStageCentralProjection E J ξ)
        (matrixStageCentralProjection F J ξ) (matrixStageCentralProjection G J ξ)).trans
        ((add_le_add hδF hδG).trans_eq (add_halves δ))
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · obtain ⟨b,hb⟩ := hF i hi
        exact ⟨b,(matrixStageCentralProjection_error_mono F G hFG J ξ (η i) b).trans hb⟩
      · exact ⟨c,hc⟩

end

end KadisonKastler

end OAI
