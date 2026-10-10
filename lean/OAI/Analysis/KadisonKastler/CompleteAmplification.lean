import OAI.Analysis.KadisonKastler.FiniteFactorAmplification
import OAI.Analysis.KadisonKastler.SquareCompleteBound

namespace OAI

/-! # The uniform completely bounded derivation estimate for II₁ factors -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance completeAmplificationSourceOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeAmplificationOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The entrywise derivation acts as commutation with the diagonal operator. -/
theorem hilbertMatrix_map_innerDerivation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : H →L[ℂ] H) (X : CStarMatrix ι ι (Algebra M)) :
    hilbertMatrix (CStarMatrix.mapₗ
      ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) X) =
      hilbertMatrix (diagonalAmplification h) * matrixOperatorHom M X -
        matrixOperatorHom M X * hilbertMatrix (diagonalAmplification h) := by
  rw [matrixOperatorHom_apply, ← hilbertMatrix_mul, ← hilbertMatrix_mul]
  have hsub := map_sub (hilbertMatrixHom (H := H) (n := ι))
    (diagonalAmplification h * X.map M.toStarSubalgebra.subtype)
    (X.map M.toStarSubalgebra.subtype * diagonalAmplification h)
  change hilbertMatrix (diagonalAmplification h * X.map M.toStarSubalgebra.subtype -
      X.map M.toStarSubalgebra.subtype * diagonalAmplification h) =
    hilbertMatrix (diagonalAmplification h * X.map M.toStarSubalgebra.subtype) -
      hilbertMatrix (X.map M.toStarSubalgebra.subtype * diagonalAmplification h) at hsub
  rw [← hsub]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change h * (X i j).val - (X i j).val * h =
    (Matrix.diagonal (fun _ : ι => h) *
      CStarMatrix.ofMatrix.symm (X.map M.toStarSubalgebra.subtype)) i j -
      (CStarMatrix.ofMatrix.symm (X.map M.toStarSubalgebra.subtype) *
        Matrix.diagonal (fun _ : ι => h)) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

/-- The bounded derivation on the original represented algebra. -/
def concreteDerivation (M : VonNeumannAlgebra H) (h : H →L[ℂ] H) :
    Algebra M →L[ℂ] (H →L[ℂ] H) :=
  ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap).mkContinuous
    (2 * ‖h‖) (fun x => by
      change ‖h * x.val - x.val * h‖ ≤ 2 * ‖h‖ * ‖x‖
      calc
        _ ≤ ‖h * x.val‖ + ‖x.val * h‖ := norm_sub_le _ _
        _ ≤ ‖h‖ * ‖x‖ + ‖x‖ * ‖h‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖h‖ * ‖x‖ := by ring)

@[simp]
theorem concreteDerivation_apply (M : VonNeumannAlgebra H) (h : H →L[ℂ] H)
    (x : Algebra M) : concreteDerivation M h x = h * x.val - x.val * h := rfl

/-- Transfer a bound on the represented matrix algebra to the abstract
entrywise matrix derivation. -/
theorem matrix_derivation_bound_of_represented_bound {n : ℕ}
    (h : H →L[ℂ] H) {c : ℝ}
    (hbound : ∀ a : Algebra (matrixVonNeumann (ι := Fin n) M),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * a.val - a.val * T‖ ≤ c * ‖a‖)
    (X : CStarMatrix (Fin n) (Fin n) (Algebra M)) :
    ‖CStarMatrix.mapₗ ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) X‖ ≤
      c * ‖X‖ := by
  have hX := hbound (matrixAlgebraEquiv M X)
  have hnorm : ‖matrixAlgebraEquiv M X‖ = ‖X‖ := by
    change ‖(matrixAlgebraEquiv M X).val‖ = ‖X‖
    rw [matrixAlgebraEquiv_apply]
    exact norm_matrixOperatorHom M X
  rw [hnorm] at hX
  rw [← norm_hilbertMatrix, hilbertMatrix_map_innerDerivation]
  simpa only [matrixAlgebraEquiv_apply] using hX

variable [TopologicalSpace.SeparableSpace H]

/-- The manuscript's uniform amplification theorem, with constant `600`.
The only assumptions beyond the represented factor are the cited published
cyclic similarity, Fock representation, ultrapower, and independence inputs. -/
theorem finiteFactor_completelyBounded_derivation
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (h : H →L[ℂ] H) (hh : h.IsSymmetric) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    CompletelyBoundedBy
      ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) (600 * δ) := by
  apply completelyBoundedBy_of_large_square
  intro n hn X
  let : NeZero n := ⟨by omega⟩
  exact matrix_derivation_bound_of_represented_bound h
    (fun a => finiteFactor_matrix_commutator_le hpub hmat hind hM hCyclic hFock
      h hh hδ hb hn a) X

/-- Uniform amplification in terms of the ordinary operator norm of the
restricted derivation, as in Theorem 3.1 of the manuscript. -/
theorem finiteFactor_uniform_amplification
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (h : H →L[ℂ] H) (hh : h.IsSymmetric) :
    CompletelyBoundedBy (concreteDerivation M h).toLinearMap
      (600 * ‖concreteDerivation M h‖) := by
  apply finiteFactor_completelyBounded_derivation hpub hmat hind hM hCyclic hFock
    h hh (norm_nonneg _)
  intro a ha
  exact (concreteDerivation M h).le_opNorm ⟨a, ha⟩

end

end KadisonKastler

end OAI
