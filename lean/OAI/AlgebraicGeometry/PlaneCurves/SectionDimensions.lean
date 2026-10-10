import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import OAI.AlgebraicGeometry.PlaneCurves.ConstantSections
import OAI.AlgebraicGeometry.PlaneCurves.Fourier
import OAI.AlgebraicGeometry.PlaneCurves.ThetaPolynomialBases

namespace OAI

/-!
# Dimensions and lower-endpoint theta bases of section spaces
-/

section

/-! Exact positive-degree dimensions for genuine automorphic sections with
arbitrary nonzero multipliers, via the proved theta coefficient basis. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09

/-- Arbitrary nonzero multipliers admit the actual positive-degree theta basis.
Only injectivity of the genuine circle coefficient map remains an explicit input. -/
theorem positiveSectionBasis_exists {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Nonempty (Basis (Fin n.toNat) ℂ (automorphicSections (τ : ℂ) n γ)) := by
  obtain ⟨σ, x₀, ε, heps, hgamma, _, hU⟩ :=
    Nagata.W02.exists_normalized_multiplier_frame (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn) hτ hτone hγ
  have heps0 : ε ≠ 0 := by intro hz; simp [hz] at heps
  let b := centeredThetaSectionBasis n hn σ x₀ heps0 heps hτ hτone (hC _ _) hU
  have hc : Fintype.card (thetaIndices (σ - x₀ * (n : ℝ)) n) = n.toNat := by
    rw [Fintype.card_coe, card_thetaIndices]
  let e : thetaIndices (σ - x₀ * (n : ℝ)) n ≃ Fin n.toNat :=
    (Fintype.equivFin _).trans (finCongr hc)
  let E : automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) ≃ₗ[ℂ]
      automorphicSections (τ : ℂ) n γ := LinearEquiv.ofEq _ _ (by rw [hgamma])
  exact ⟨(b.map E).reindex e⟩

def positiveSectionBasisFin {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Basis (Fin n.toNat) ℂ (automorphicSections (τ : ℂ) n γ) :=
  Classical.choice (positiveSectionBasis_exists hτ hτone hC hn hγ)

theorem positiveSection_finite {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Finite ℂ (automorphicSections (τ : ℂ) n γ) :=
  Module.Finite.of_basis (positiveSectionBasisFin hτ hτone hC hn hγ)

theorem positiveSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) n γ) = n.toNat := by
  rw [Module.finrank_eq_card_basis (positiveSectionBasisFin hτ hτone hC hn hγ), Fintype.card_fin]

/-- The constant tip has dimension one unconditionally. -/
theorem zeroSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) 0 1) = 1 := by
  rw [Module.finrank_eq_card_basis (Nagata.W19.degreeZeroConstantBasis.{0} hτ hτone)]
  exact Fintype.card_punit

end Nagata.Workers.W10

end
end

section

/-! The source-compatible form of the genuine centered theta basis, parameterized
by the literal lower endpoint U. Only actual Laurent injectivity remains explicit. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W07 Nagata.W08 Nagata.W09

def thetaLowerIndexEquiv (U x₀ : ℝ) (n : ℤ) :
    thetaIndices ((U + x₀ * (n : ℝ)) - x₀ * (n : ℝ)) n ≃ thetaIndices U n :=
  Equiv.subtypeEquivRight (fun K => by rw [add_sub_cancel_right])

def thetaSectionBasisAtLower (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (thetaIndices U n) ℂ
      (automorphicSections (τ : ℂ) n (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))) :=
  (centeredThetaSectionBasis n hn (U + x₀ * (n : ℝ)) x₀ hε hunit hτ hτone hC
    (by simpa only [add_sub_cancel_right] using hU)).reindex (thetaLowerIndexEquiv U x₀ n)

@[simp] theorem thetaSectionBasisAtLower_apply (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) (K : thetaIndices U n) :
    thetaSectionBasisAtLower n hn U x₀ hε hunit hτ hτone hC hU K =
      normalizedSourceThetaSection n K.val hn (U + x₀ * (n : ℝ)) x₀ hε hτ hτone := by
  simp only [thetaSectionBasisAtLower, Basis.reindex_apply, centeredThetaSectionBasis_apply]
  rfl

theorem thetaSectionBasisAtLower_local (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) (K : thetaIndices U n) (x : ℂ) :
    (thetaSectionBasisAtLower n hn U x₀ hε hunit hτ hτone hC hU K).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (n : ℝ) ((K.val : ℝ) - U) (K.val : ℝ) ε τ x := by
  rw [thetaSectionBasisAtLower_apply, normalizedSourceThetaSection_centered]
  have ha : (K.val : ℝ) - (U + x₀ * (n : ℝ)) + x₀ * (n : ℝ) = (K.val : ℝ) - U := by ring
  rw [ha]
  rfl

end Nagata.Workers.W10

end
end

section

noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08

def automorphicSectionBasis {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Basis (Fin n.toNat) ℂ (automorphicSections (τ : ℂ) n γ) :=
  positiveSectionBasisFin hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ)) hn hγ

theorem automorphicSection_finite {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Finite ℂ (automorphicSections (τ : ℂ) n γ) :=
  positiveSection_finite hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ)) hn hγ

theorem automorphicSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) n γ) = n.toNat :=
  positiveSection_finrank hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ)) hn hγ

/-- The exact centered source vectors, retaining their local scalar normalization. -/
def actualThetaBasis (n : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hU : σ - x₀ * (n : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (Nagata.W09.thetaIndices (σ - x₀ * (n : ℝ)) n) ℂ
      (automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))) :=
  centeredThetaSectionBasis n hn σ x₀ hε hunit hτ hτone
    (Nagata.W01.laurentCoefficientMap_injective _ _ _) hU

@[simp] theorem actualThetaBasis_apply (n : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hU : σ - x₀ * (n : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ))
    (K : Nagata.W09.thetaIndices (σ - x₀ * (n : ℝ)) n) :
    actualThetaBasis n hn σ x₀ hε hunit hτ hτone hU K =
      Nagata.W09.normalizedSourceThetaSection n K.val hn σ x₀ hε hτ hτone :=
  centeredThetaSectionBasis_apply _ _ _ _ _ _ _ _ _ _ K

end Nagata.Workers.W10

end
end

end OAI
