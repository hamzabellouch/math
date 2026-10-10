import OAI.Analysis.KadisonKastler.AmenableMatrixStability
import OAI.Analysis.KadisonKastler.UCPDescent

namespace OAI

/-! # Descending the finite-corner construction

The upper algebras are concrete algebras on a second Hilbert space. An
actual UCP retraction of the ambient embedding returns their conjugacy
to the original representation. The hypotheses below are the data needed
from the crossed-product construction, not a stability assertion about it.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

local instance matrixDescentOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance matrixDescentStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance matrixDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

def matrixDescentError (t : ℝ) : ℝ := 256 * matrixCornerError t

theorem continuous_matrixDescentError : Continuous matrixDescentError :=
  continuous_const.mul continuous_matrixCornerError

@[simp] theorem matrixDescentError_zero : matrixDescentError 0 = 0 := by
  simp [matrixDescentError]

theorem matrixDescentError_monotone : Monotone matrixDescentError := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (matrixCornerError_monotone hab) (by norm_num)

/-- The concrete finite-corner conjugacy descends through a UCP retraction
whose restriction to the upper target lands in the original target. -/
theorem spatial_of_retracted_matrix_algebras
    (h : FiniteFactorPublishedInputs.{v})
    (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (R : (K →L[ℂ] K) →CP (H →L[ℂ] H)) (hR : R 1 = 1)
    (hfix : ∀ x, R (j x) = x)
    (A B S : VonNeumannAlgebra K) (hSA : S ≤ A) (hS : IsInjective S)
    (E : Submodule ℂ K) [CompleteSpace E] (F : FullMatrixCorner E)
    (hFS : ∀ i k, F.entry i k ∈ S)
    (hCorner : Generator.IsII1Factor
      (representedCorner E A (F.zero_zero ▸ hSA (hFS 0 0))).toStarSubalgebra)
    (hMA : ∀ x : Algebra M, j x ∈ A)
    (hBN : ∀ y ∈ B, R y ∈ N)
    {t : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgap : kkDistance M N < t) (hgapUp : kkDistance A B < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ matrixDescentError t := by
  obtain ⟨z, hz, hn⟩ := F.spatial_of_injective_matrix_subalgebra h A B S hSA hS hFS
    hCorner ht htEmbed htPosition hgapUp htStandard htSpatial
  have hmem (x : Algebra M) :
      R ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) ∈ N := by
    apply hBN
    change unitaryConj z (j x) ∈ (B : Set (K →L[ℂ] K))
    rw [← hz]
    exact ⟨j x, hMA x, rfl⟩
  obtain ⟨u, hu, huNorm⟩ := concrete_unitary_of_retracted_conjugation
    hCorrection hCommutant j hj R hR hfix z hmem hgap (by linarith) (by linarith)
  exact ⟨u, hu, huNorm.trans (mul_le_mul_of_nonneg_left hn (by norm_num))⟩

end

end KadisonKastler

end OAI
