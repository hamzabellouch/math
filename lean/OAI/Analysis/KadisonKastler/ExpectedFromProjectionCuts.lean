import OAI.Analysis.KadisonKastler.ExpectedFromContraction

namespace OAI

/-! # Projection cuts close the expected-subfactor construction

Inserting a projection with a fixed commutator gap into a finite matrix
algebra contracts the discarded energy. A nearby reference vector in
the central-vector space allows geometric iteration.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_projection_cuts_with_gap
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖ = 1)
    (d : ModularConjugationData M ξ)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hcut : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      inner ℂ η (matrixStageCentralProjection E d.conjugation ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ (F : FiniteMatrixStage M) (p : AlgebraProjection M) (ζ : H),
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        p.val.val ∈ F.units.concreteAlgebra ∧
        ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation ∧
        ‖matrixStageCentralProjection E d.conjugation ξ - ζ‖ ≤ δ ∧
        γ * ‖η‖ ^ 2 ≤
          ‖p.val.val η - conjugationOperator d.conjugation p.val.val η‖ ^ 2) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  apply expectedMatrixSubfactorModel_of_central_contraction hM ξ hunit d
    (Real.sqrt (1-γ)) (Real.sqrt_nonneg _)
    ((Real.sqrt_lt (sub_nonneg.mpr hγ1.le) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by linarith))
  intro E η hη horth δ hδ
  obtain ⟨F,p,ζ,hEF,hp,hζ,hclose,hgap⟩ := hcut E η hη horth δ hδ
  refine ⟨F,hEF,?_,?_⟩
  · have hcomp : matrixStageCentralProjection F d.conjugation ∘L
        matrixStageCentralProjection E d.conjugation = matrixStageCentralProjection F d.conjugation :=
      Submodule.starProjection_comp_starProjection_of_le
        (centralVectorSpace_antitone hEF d.conjugation)
    have hn := centralProjection_displacement_le_of_central_vector
      (centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation)
      (matrixStageCentralProjection E d.conjugation ξ) ζ hζ
    have he := congrArg (fun T : H →L[ℂ] H => T ξ) hcomp
    change matrixStageCentralProjection F d.conjugation
      (matrixStageCentralProjection E d.conjugation ξ) =
        matrixStageCentralProjection F d.conjugation ξ at he
    change ‖matrixStageCentralProjection E d.conjugation ξ -
      matrixStageCentralProjection F d.conjugation
        (matrixStageCentralProjection E d.conjugation ξ)‖ ≤ _ at hn
    rw [he] at hn
    exact hn.trans hclose
  · have he := matrixStageCentralProjection_contraction F d.conjugation d.involutive
      (d.right_mem le_rfl) p hp η γ hgap
    have hroot : Real.sqrt (1-γ) ^ 2 = 1-γ := Real.sq_sqrt (sub_nonneg.mpr hγ1.le)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,hroot]
    exact he

theorem expectedMatrixSubfactorModel_of_projection_cuts
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖ = 1)
    (d : ModularConjugationData M ξ)
    (hcut : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      inner ℂ η (matrixStageCentralProjection E d.conjugation ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ (F : FiniteMatrixStage M) (p : AlgebraProjection M) (ζ : H),
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        p.val.val ∈ F.units.concreteAlgebra ∧
        ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation ∧
        ‖matrixStageCentralProjection E d.conjugation ξ - ζ‖ ≤ δ ∧
        (1 / 32 : ℝ) * ‖η‖ ^ 2 ≤
          ‖p.val.val η - conjugationOperator d.conjugation p.val.val η‖ ^ 2) :
    Nonempty (ExpectedMatrixSubfactorModel M) :=
  expectedMatrixSubfactorModel_of_projection_cuts_with_gap hM ξ hunit d (1/32)
    (by norm_num) (by norm_num) hcut

end

end KadisonKastler

end OAI
