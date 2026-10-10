import OAI.Analysis.KadisonKastler.BlockAmplification
import OAI.Analysis.KadisonKastler.Intertwiner
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-!
# Close representations from the published commutant-distance formula

The explicit input `PublishedBlockCommutantApproximation` is the block
specialization of Arveson's distance formula, in the form of Christensen,
*Perturbations of operator algebras II*, Indiana Univ. Math. J. 26 (1977),
Proposition 2.1. See also Christensen--Sinclair--Smith--White,
*Perturbations of C*-algebraic invariants*, GAFA 20 (2010), equation (2.1),
and Cameron et al., *Kadison--Kastler stable factors* (2014), equation (2.2).

The 2010 formulation applies to represented C*-algebras. Passing through
the quotient by the representation kernel gives the formulation below
with the complete bound on the source algebra. No normality is required.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The spatial derivation implemented by `T`. -/
def innerDerivation (T : R) : R →ₗ[ℂ] R :=
  LinearMap.mulLeft ℂ T - LinearMap.mulRight ℂ T

@[simp]
theorem innerDerivation_apply (T x : R) : innerDerivation T x = T * x - x * T := rfl

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The diagonal pair of two star representations. -/
def pairedRepresentation (ρ θ : A →⋆ₐ[ℂ] B) :
    A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B :=
  (diagonalStarAlgHom (Fin 2)).comp
    { AlgHom.pi ![ρ.toAlgHom, θ.toAlgHom] with
      map_star' x := by
        ext i
        fin_cases i <;> simp
        · exact map_star ρ x
        · exact map_star θ x }

@[simp]
theorem pairedRepresentation_apply (ρ θ : A →⋆ₐ[ℂ] B) (x : A) :
    pairedRepresentation ρ θ x = blockDiagonal (ρ x) (θ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem innerDerivation_flip_diagonal (a b : B) :
    innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)
      (blockDiagonal a b) = offDiagonalLinearMap (a - b) := by
  rw [offDiagonalLinearMap_apply]
  ext i j
  simp only [innerDerivation_apply, CStarMatrix.sub_apply, CStarMatrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [blockFlip, blockDiagonal, blockOffDiagonal]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem pairedRepresentation_commutator_bound (ρ θ : A →⋆ₐ[ℂ] B) {e : ℝ}
    (hclose : CompletelyBoundedBy (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) e) :
    CompletelyBoundedBy
      ((innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)).comp
        (pairedRepresentation ρ θ).toAlgHom.toLinearMap) e := by
  have hid :
      (innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)).comp
        (pairedRepresentation ρ θ).toAlgHom.toLinearMap =
      offDiagonalLinearMap.comp (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) := by
    apply LinearMap.ext
    intro x
    change innerDerivation
      (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)
      (pairedRepresentation ρ θ x) = offDiagonalLinearMap (ρ x - θ x)
    rw [pairedRepresentation_apply]
    exact innerDerivation_flip_diagonal (ρ x) (θ x)
  rw [hid]
  exact (completelyBoundedBy_offDiagonal_iff _ e).mpr hclose

variable (A) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (K →L[ℂ] K) := CStarAlgebra.spectralOrderedRing _

/-- The precise strict-approximation consequence of the published
commutant-distance formula, restricted to two-by-two operator matrices. -/
def PublishedBlockCommutantApproximation : Prop :=
  ∀ (π : A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K))
    (T : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K)) (e : ℝ), 0 ≤ e →
    CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e →
    ∀ r : ℝ, e / 2 < r →
      ∃ D : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K),
        (∀ x, D * π x = π x * D) ∧ ‖D - T‖ < r

variable {A K}

/-- Completely close representations are conjugate by a unitary close
to the identity, conditional only on the published distance formula. -/
theorem close_representations_of_published
    (hPublished : PublishedBlockCommutantApproximation A K)
    (ρ θ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 4)
    (hclose : CompletelyBoundedBy (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) e) :
    ∃ u : unitary (K →L[ℂ] K),
      (∀ x, (u : K →L[ℂ] K) * ρ x * star (u : K →L[ℂ] K) = θ x) ∧
      ‖(u : K →L[ℂ] K) - 1‖ ≤ 4 * e := by
  by_cases hezero : e = 0
  · have heq : ∀ x, ρ x = θ x := by
      intro x
      have h := hclose 1 1 (CStarMatrix.toOneByOne (Fin 1) ℂ A x)
      rw [hezero, zero_mul] at h
      have hm := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      have hx := congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) (K →L[ℂ] K) => M 0 0) hm
      change ρ x - θ x = 0 at hx
      exact sub_eq_zero.mp hx
    exact ⟨1, by simpa using heq, by simp [hezero]⟩
  have hep : 0 < e := lt_of_le_of_ne he (Ne.symm hezero)
  let π := pairedRepresentation ρ θ
  let S : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) :=
    blockFlip (A := K →L[ℂ] K)
  obtain ⟨D, hcomm, hDS⟩ := hPublished π S e he
    (pairedRepresentation_commutator_bound ρ θ hclose) (2 * e) (by linarith)
  have hT : ∀ x, D 1 0 * ρ x = θ x * D 1 0 := by
    intro x
    exact block_commute_intertwines D (ρ x) (θ x)
      (by simpa only [π, pairedRepresentation_apply] using hcomm x)
  have hTnorm : ‖D 1 0 - 1‖ < 2 * e :=
    (norm_lowerLeft_sub_one_le D).trans_lt hDS
  have hnear : ‖D 1 0 - 1‖ < 1 := by linarith
  obtain ⟨u, hu, hnorm⟩ := exists_near_unitary_conjugating ρ θ hT hnear
  exact ⟨u, hu, by linarith⟩

end

end KadisonKastler

end OAI
