import OAI.Analysis.Nuclearity.CPMatrixFunctional
import OAI.Analysis.OInfinity.FockCompression
import OAI.Analysis.PureInfiniteness.TwoMatrixNuclear

namespace OAI

/-! A positive functional on a matrix algebra yields a completely positive
map into scalar matrices. The construction uses its GNS representation and
a finite family of matrix-unit vectors. -/

noncomputable section
open scoped InnerProductSpace CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {n : ℕ}

local instance matrixFunctionalRealModule : Module ℝ (CStarMatrix (Fin n) (Fin n) A) :=
  Module.complexToReal _

def matrixSingle (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixSingle_star (i j : Fin n) (a : A) :
    star (matrixSingle i j a) = matrixSingle j i (star a) := by
  change Matrix.conjTranspose (Matrix.single i j a) = Matrix.single j i (star a)
  exact Matrix.conjTranspose_single _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixSingle_mul (i j k : Fin n) (a b : A) :
    matrixSingle i j a * matrixSingle j k b = matrixSingle i k (a * b) := by
  classical
  change Matrix.single i j a * Matrix.single j k b = Matrix.single i k (a * b)
  exact Matrix.single_mul_single_same (c := a) i j k b

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixDiagonal_mul_single (i j : Fin n) (a b : A) :
    matrixDiagonalHom (n := Fin n) a * matrixSingle i j b = matrixSingle i j (a * b) := by
  ext k l
  change (Matrix.diagonal (fun _ : Fin n => a) * Matrix.single i j b) k l =
    Matrix.single i j (a * b) k l
  rw [Matrix.diagonal_mul]
  simp only [Matrix.single_apply]
  split_ifs <;> simp

section Synthesis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteVectorSynthesis (v : Fin n → H) : EuclideanSpace ℂ (Fin n) →L[ℂ] H where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]
  cont := by fun_prop

@[simp] lemma finiteVectorSynthesis_basis (v : Fin n → H) (i : Fin n) :
    finiteVectorSynthesis v (EuclideanSpace.basisFun (Fin n) ℂ i) = v i := by
  simp [finiteVectorSynthesis, EuclideanSpace.basisFun_apply, PiLp.single_apply]
end Synthesis

private def matrixFunctionalVectors (p : Fin n)
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) : Fin n → σ.GNS :=
  fun i => (σ.toPreGNS (matrixSingle p i 1) : σ.GNS)

private def matrixFunctionalRepresentation
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) : A →⋆ₙₐ[ℂ] (σ.GNS →L[ℂ] σ.GNS) :=
  σ.gnsNonUnitalStarAlgHom.comp matrixDiagonalHom

def matrixFunctionalCP (p : Fin n)
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) :
    A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ :=
  (starHomContinuousLinear (scalarMatrixOperatorEquiv (Fin n)).symm.toStarAlgHom.toNonUnitalStarAlgHom).comp
    (hilbertCompression (matrixFunctionalRepresentation σ)
      (finiteVectorSynthesis (matrixFunctionalVectors p σ)))

theorem matrixFunctionalCP_completelyPositive (p : Fin n)
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) :
    CompletelyPositive (matrixFunctionalCP p σ) :=
  completelyPositive_comp _ _ (hilbertCompression_cp _ _)
    (starHomContinuous_completelyPositive _)

theorem matrixFunctionalCP_entry (p : Fin n)
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (a : A) (i j : Fin n) :
    matrixFunctionalCP p σ a i j = σ (matrixSingle i j a) := by
  change (scalarMatrixOperatorEquiv (Fin n)).symm
    ((finiteVectorSynthesis (matrixFunctionalVectors p σ)).adjoint.comp
      (((matrixFunctionalRepresentation σ) a).comp
        (finiteVectorSynthesis (matrixFunctionalVectors p σ)))) i j = _
  rw [scalarMatrixOperatorEquiv_symm_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    finiteVectorSynthesis_basis]
  change inner ℂ (σ.toPreGNS (matrixSingle p i 1) : σ.GNS)
    (σ.gnsNonUnitalStarAlgHom (matrixDiagonalHom a)
      (σ.toPreGNS (matrixSingle p j 1) : σ.GNS)) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := σ.PreGNS)]
  simp only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.leftMulMapPreGNS_apply, PositiveLinearMap.ofPreGNS_toPreGNS]
  change σ (star (matrixSingle p i 1) * (matrixDiagonalHom a * matrixSingle p j 1)) = _
  rw [matrixSingle_star, star_one, matrixDiagonal_mul_single, matrixSingle_mul, one_mul, mul_one]

/-- The reconstructed map has a concrete unital Stinespring representation.
Only its value at the unit is needed to bound the compression operator. -/
theorem matrixFunctionalCP_exists_dilation (p : Fin n)
    (σ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (hn : ‖matrixFunctionalCP p σ 1‖ ≤ 1) :
    ∃ (H : ComplexHilbert.{u}), ∃ (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      ∃ (V : EuclideanSpace ℂ (Fin n) →L[ℂ] H), ‖V‖ ≤ 1 ∧
        ∀ a, scalarMatrixOperatorEquiv (Fin n) (matrixFunctionalCP p σ a) =
          V.adjoint.comp ((π a).comp V) := by
  let H : ComplexHilbert := ⟨σ.GNS⟩
  let δ : A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
    { matrixDiagonalHom with
      map_one' := by ext i j; rfl
      commutes' := fun c => by
        ext i j
        change (if i = j then algebraMap ℂ A c else 0) =
          if i = j then algebraMap ℂ A c else 0
        rfl }
  let π : A →⋆ₐ[ℂ] (H →L[ℂ] H) := σ.gnsStarAlgHom.comp δ
  let V : EuclideanSpace ℂ (Fin n) →L[ℂ] H :=
    finiteVectorSynthesis (matrixFunctionalVectors p σ)
  have he (a : A) : scalarMatrixOperatorEquiv (Fin n) (matrixFunctionalCP p σ a) =
      V.adjoint.comp ((π a).comp V) := by
    change scalarMatrixOperatorEquiv (Fin n) ((scalarMatrixOperatorEquiv (Fin n)).symm
      (V.adjoint.comp ((π a).comp V))) = _
    exact (scalarMatrixOperatorEquiv (Fin n)).apply_symm_apply _
  have hVV : V.adjoint.comp V =
      scalarMatrixOperatorEquiv (Fin n) (matrixFunctionalCP p σ 1) := by
    simpa only [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      using (he 1).symm
  have hnorm : ‖V‖ * ‖V‖ ≤ 1 := by
    rw [← ContinuousLinearMap.norm_adjoint_comp_self, hVV,
      StarAlgEquiv.norm_map]
    exact hn
  exact ⟨H, π, V, by nlinarith [norm_nonneg V], he⟩

end WeakPureInfiniteness

end

end OAI
