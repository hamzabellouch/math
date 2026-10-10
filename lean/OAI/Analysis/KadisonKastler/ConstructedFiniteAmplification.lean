import OAI.Analysis.KadisonSimilarity.FreeProduct.FiniteFactorFreeness
import OAI.Analysis.KadisonKastler.CompleteAmplification

namespace OAI

/-! # The constructed finite-factor estimate in the stability notation

The finite-factor commutator estimate is uniform over separable
representations. Square matrix estimates imply the rectangular
complete bound used in strong stability.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance constructedFiniteSourceOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance constructedFiniteSourceStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
local instance constructedFiniteOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance constructedFiniteOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- A commutator estimate uniform over separably represented finite factors. -/
theorem constructed_finiteFactor_estimate (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    KadisonSimilarity.CommutatorEstimate M (3 * KadisonSimilarity.cornerConstant + 2) := by
  classical
  rcases subsingleton_or_nontrivial H with h | h
  · let _ := h
    exact (hM.nonzero (Subsingleton.elim _ _)).elim
  · let _ := h
    obtain ⟨F⟩ := KadisonSimilarity.exists_finiteFactorPresentation M hM
    obtain ⟨ω, hω⟩ := Ultrafilter.exists_le (Filter.cofinite : Filter ℕ)
    exact (F.model ω hω (F.freePosition ω hω)).estimate

/-- A numerical upper bound for the finite-factor commutator constant. -/
theorem constructed_finiteFactor_constant_le :
    3 * KadisonSimilarity.cornerConstant + 2 ≤ (1000000 : ℝ) := by
  have hs : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hr0 : 0 ≤ KadisonSimilarity.rowConstant := KadisonSimilarity.rowConstant_pos.le
  have hr : KadisonSimilarity.rowConstant ≤ 6 := by
    unfold KadisonSimilarity.rowConstant
    linarith
  have hc0 : 0 ≤ KadisonSimilarity.cyclicConstant := KadisonSimilarity.cyclicConstant_pos.le
  have hc : KadisonSimilarity.cyclicConstant ≤ 625 := by
    unfold KadisonSimilarity.cyclicConstant
    nlinarith
  have hp0 := Real.pi_pos
  have hp := Real.pi_lt_four
  have hp2 : Real.pi ^ 2 ≤ 16 := by nlinarith
  have hprod : Real.pi ^ 2 * (1 + 4 * KadisonSimilarity.cyclicConstant) ≤ 16 * 2501 :=
    mul_le_mul hp2 (by linarith) (by positivity) (by norm_num)
  unfold KadisonSimilarity.cornerConstant
  nlinarith

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The two concrete definitions of an operator matrix have the same action. -/
theorem similarity_matrixOperator_eq {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    KadisonSimilarity.matrixOperator (fun i j => X i j) = hilbertMatrix X := rfl

/-- Convert the proved finite square estimates to all rectangular levels. -/
theorem constructed_finiteFactor_completelyBounded
    (M : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖T * a - a * T‖ ≤ δ * ‖a‖) :
    CompletelyBoundedBy ((innerDerivation T).comp M.toStarSubalgebra.subtype.toLinearMap)
      (1000000 * δ) := by
  have hscalar : KadisonSimilarity.scalarCommutatorNorm M T ≤ δ :=
    (KadisonSimilarity.scalarCommutatorNorm_le_iff M T hδ).mpr hb
  have hestimate := constructed_finiteFactor_estimate M hM
  apply completelyBoundedBy_of_large_square
  intro n _ X
  let Y : Matrix (Fin n) (Fin n) (H →L[ℂ] H) := fun i j => (X i j).val
  have h := hestimate T n Y (fun i j => (X i j).property)
  have hmatrix : KadisonSimilarity.matrixOperator Y = matrixOperatorHom M X := rfl
  have hcomm : KadisonSimilarity.commutator (KadisonSimilarity.amplify T n)
      (KadisonSimilarity.matrixOperator Y) =
      hilbertMatrix (CStarMatrix.mapₗ
        ((innerDerivation T).comp M.toStarSubalgebra.subtype.toLinearMap) X) := by
    rw [KadisonSimilarity.commutator_amplify_matrixOperator]
    rfl
  rw [hcomm, norm_hilbertMatrix, hmatrix, norm_matrixOperatorHom] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul constructed_finiteFactor_constant_le hscalar
      (KadisonSimilarity.scalarCommutatorNorm_nonneg M T) (by norm_num)) (norm_nonneg X))

end

end KadisonKastler

end OAI
