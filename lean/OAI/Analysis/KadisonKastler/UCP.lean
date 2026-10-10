import OAI.Analysis.KadisonKastler.PublishedCorrection
import OAI.Analysis.KadisonKastler.CompletelyPositive
import OAI.Analysis.KadisonKastler.FaithfulRepresentation
import OAI.Analysis.KadisonKastler.Range

namespace OAI

/-!
# From a close UCP map to a star-algebra equivalence

The range argument and the multiplication-correction estimates give the
isomorphism part of the manuscript's UCP criterion under
`PublishedMultiplicationCorrection`. Complete positivity gives complete
contractivity and star preservation.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A complete bound implies the corresponding scalar bound. -/
theorem norm_le_of_completelyBoundedBy (F : A →ₗ[ℂ] B) {c : ℝ}
    (hF : CompletelyBoundedBy F c) (x : A) : ‖F x‖ ≤ c * ‖x‖ := by
  let eA := CStarMatrix.toOneByOne (Fin 1) ℂ A
  let eB := CStarMatrix.toOneByOne (Fin 1) ℂ B
  have heq : CStarMatrix.mapₗ F (eA x) = eB (F x) := by
    ext i j
    rfl
  have h := hF 1 1 (eA x)
  have hnA : ‖eA x‖ = ‖x‖ :=
    NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective x
  have hnB : ‖eB (F x)‖ = ‖F x‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective (F x)
  rw [heq, hnA, hnB] at h
  exact h

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A UCP map completely close to a faithful representation and with
strict reverse unit-ball gap is bijective. Its normality is not needed. -/
theorem bijective_ucp_of_reverse_gap (M : VonNeumannAlgebra H)
    (φ : Algebra M →CP B) (hφ : φ 1 = 1)
    (ρ : Algebra M →⋆ₐ[ℂ] C) (ι : B →⋆ₐ[ℂ] C)
    (hρ : Function.Injective ρ) (hι : Function.Injective ι)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      (ι.toAlgHom.toLinearMap.comp φ.toLinearMap - ρ.toAlgHom.toLinearMap) e)
    (hgap : ∀ y : B, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    Function.Bijective φ := by
  apply bijective_of_close_isometry_and_reverse_gap
    (starAlgHomToContinuousLinearMap ρ) (starAlgHomToContinuousLinearMap ι)
    (unitalCompletelyPositiveToContinuousLinearMap φ hφ)
    (injective_starAlgHom_norm ρ hρ) (injective_starAlgHom_norm ι hι) he he₁ hge
  · exact fun x => norm_le_of_completelyBoundedBy _ hclose x
  · exact hgap

/-- The complete `32e` isomorphism conclusion of the UCP criterion.
The source is a concrete von Neumann algebra; the target may be any
faithfully represented C*-algebra. Multiplication correction gives the
star-algebra equivalence. -/
theorem ucp_starEquiv_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (φ : Algebra M →CP B) (hφ : φ 1 = 1)
    (ρ : Algebra M →⋆ₐ[ℂ] C) (ι : B →⋆ₐ[ℂ] C)
    (hρ : Function.Injective ρ) (hι : Function.Injective ι)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      (ι.toAlgHom.toLinearMap.comp φ.toLinearMap - ρ.toAlgHom.toLinearMap) e)
    (hgap : ∀ y : B, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] B,
      CompletelyBoundedBy
        (ι.toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap - ρ.toAlgHom.toLinearMap)
        (32 * e) := by
  have hbij := bijective_ucp_of_reverse_gap M φ hφ ρ ι hρ hι he
    (by linarith) hge hclose hgap
  let F : Algebra M ≃ₗ[ℂ] B := LinearEquiv.ofBijective φ.toLinearMap hbij
  exact corrected_equivalence_of_published M hPublished F ρ.toAlgHom ι.toAlgHom
    (completelyPositive_map_star φ) he he₁
    (injective_starAlgHom_completelyIsometric ρ hρ)
    (injective_starAlgHom_completelyIsometric ι hι)
    (unital_completelyPositive_completelyBoundedBy φ hφ) hclose

end

end KadisonKastler

end OAI
