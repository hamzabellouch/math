import OAI.AlgebraicGeometry.PlaneCurves.PolynomialBlocks
import OAI.AlgebraicGeometry.PlaneCurves.ThetaCoefficients

namespace OAI

/-!
# Specialized theta and polynomial bases of section spaces
-/

section

/-! The actual polynomial-section space has the finite coefficient-product
presentation proved in PolynomialBlocks. No theta basis or dimension is assumed
in that equivalence. The subsequent basis constructor states all still-needed
coefficient-map inputs explicitly. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces

def polynomialSectionCoordinates (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    polynomialSections τ γL γP d m P ≃ₗ[ℂ]
      ((j : Fin ((d / 3).toNat + 1)) → coefficientSpace τ γL γP d m (j.val : ℤ) P) :=
  boundedPolynomialEquiv (d / 3).toNat
    (fun j => coefficientSpace τ γL γP d m (j : ℤ) P)

@[simp] theorem polynomialSectionCoordinates_apply
    (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (F : polynomialSections τ γL γP d m P) (j : Fin ((d / 3).toNat + 1)) :
    (polynomialSectionCoordinates τ γL γP d m P F j).val = F.val.coeff j.val := rfl

/-- Conditional assembly from actual block coefficient maps and actual delta
vectors. Each analytic input is exposed; no branch basis is supplied as a field. -/
def polynomialSectionBasisFromCoefficients (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (I : Fin ((d / 3).toNat + 1) → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (c : ∀ j, coefficientSpace τ γL γP d m (j.val : ℤ) P →ₗ[ℂ] (I j → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (v : ∀ j, I j → coefficientSpace τ γL γP d m (j.val : ℤ) P)
    (hv : ∀ j i, c j (v j i) = Pi.single i 1) :
    Basis (Σ j, I j) ℂ (polynomialSections τ γL γP d m P) :=
  boundedPolynomialBasis (d / 3).toNat
    (fun j => coefficientSpace τ γL γP d m (j : ℤ) P) I
    (fun j => basisFromCoefficients (c j) (hc j) (v j) (hv j))

/-- Every basis vector is the literal fiber monomial with its actual block section. -/
theorem polynomialSectionBasis_as_monomial (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (I : Fin ((d / 3).toNat + 1) → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (c : ∀ j, coefficientSpace τ γL γP d m (j.val : ℤ) P →ₗ[ℂ] (I j → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (v : ∀ j, I j → coefficientSpace τ γL γP d m (j.val : ℤ) P)
    (hv : ∀ j i, c j (v j i) = Pi.single i 1)
    (j : Fin ((d / 3).toNat + 1)) (i : I j) :
    (polynomialSectionBasisFromCoefficients τ γL γP d m P I c hc v hv ⟨j, i⟩).val =
      Polynomial.monomial j.val (v j i).val := by
  change (boundedPolynomialBasis (d / 3).toNat
    (fun degree => coefficientSpace τ γL γP d m (degree : ℤ) P) I
    (fun index => basisFromCoefficients (c index) (hc index) (v index) (hv index))
    ⟨j, i⟩).val = _
  rw [boundedPolynomialBasis_as_monomial, basisFromCoefficients_apply]

end Nagata.Workers.W10

end
end

section

noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W07 Nagata.W08 Nagata.W09

variable (n : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
  {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
  {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))))
  (hU : σ - x₀ * (n : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ))

/-- The genuine centered source theta family is a basis for every real
parameter 0 < tau < 1, with the literal nonintegral residue interval. -/
def centeredThetaSectionBasis :
    Basis (thetaIndices (σ - x₀ * (n : ℝ)) n) ℂ
      (automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))) := by
  have hγ : ε * ((τ ^ σ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hε (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ σ)))
  apply basisFromSupportedOrbits (laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)))
    (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) (σ - x₀ * (n : ℝ)) n
    (fun K => ((τ ^ (-x₀ * (K.val : ℝ)) : ℝ) : ℂ))
    (fun K => normalization_scalar_ne_zero hτ x₀ K.val)
    (residueCoefficientMap_injective _ hC (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) hγ _ hn
      (laurentCoefficientMap_recurrence_pos_real hτ n _ hγ))
    (fun K => normalizedSourceThetaSection n K.val hn σ x₀ hε hτ hτone)
  intro K k
  have hmem := (mem_thetaIndices_iff hU).mp K.property
  exact laurentCoefficientMap_normalizedSourceThetaSection_all_tau n K.val hn σ x₀ hε hunit
    hτ hτone (by linarith [hmem.1]) (by linarith [hmem.2]) k

@[simp] theorem centeredThetaSectionBasis_apply
    (K : thetaIndices (σ - x₀ * (n : ℝ)) n) :
    centeredThetaSectionBasis n hn σ x₀ hε hunit hτ hτone hC hU K =
    normalizedSourceThetaSection n K.val hn σ x₀ hε hτ hτone := by
  unfold centeredThetaSectionBasis
  exact basisFromSupportedOrbits_apply _ _ _ _ _ _ _ _ _ _ K

/-- Exact source series expression of the actual constructed basis vector. -/
theorem centeredThetaSectionBasis_local
    (K : thetaIndices (σ - x₀ * (n : ℝ)) n) (x : ℂ) :
    (centeredThetaSectionBasis n hn σ x₀ hε hunit hτ hτone hC hU K).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
    ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K.val : ℝ) - σ + x₀ * (n : ℝ))
      (K.val : ℝ) ε τ p x := by
  rw [centeredThetaSectionBasis_apply]
  exact normalizedSourceThetaSection_centered n K.val hn σ x₀ hε hτ hτone x

end Nagata.Workers.W10

end
end

end OAI
