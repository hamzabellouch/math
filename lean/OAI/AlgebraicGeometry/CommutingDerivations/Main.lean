import OAI.AlgebraicGeometry.CommutingDerivations.CoefficientInstances
import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization
import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedKernelIntersection
import OAI.AlgebraicGeometry.CommutingDerivations.FamilyFromLocalization
import OAI.AlgebraicGeometry.CommutingDerivations.KernelObstruction

namespace OAI

/-!
Commuting locally nilpotent derivations for the explicit Abhyankar polynomial
in every dimension `n ≥ 4`, with common kernel `ℂ[Fₙ]`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem commuting_derivations_all_dimensions (n : ℕ) (hn : 4 ≤ n) :
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) := by
  let := extendedAlgebra hn
  let := extendedScalarTower hn
  let := extended_isLocalization hn
  let : IsLocalization.Away (extendedAmbientParameter hn) (ExtendedLocalizedAmbient n) := by
    change IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n)
    exact extended_isLocalization hn
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) ℂ) (ExtendedLocalizedAmbient n)) :=
    extendedParameter_localization_injective hn (ExtendedLocalizedAmbient n)
  obtain ⟨N, d, hdesc, hfix, hcomm, hnil, hind, hker⟩ :=
    exists_commuting_family_of_localization (extendedF hn + 1) hinj
      (extendedLocalizationEquiv hn) coefficientC
      (extendedLocalizationEquiv_c hn)
      (Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)))
      (extended_localization_kernel_intersection hn)
  refine ⟨d, hfix, hcomm, hnil, hind, hker, ?_⟩
  intro g hg
  apply element_of_extendedF_subring_not_coordinate hn g
  have hmem := (hker g).mp hg
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

theorem extendedF_four : extendedF (by decide : 4 ≤ 4) = F := by
  have hi : fourInclusion (by decide : 4 ≤ 4) = id := by
    funext i
    apply Fin.ext
    rfl
  unfold extendedF
  rw [hi, rename_id]
  rfl

/-- Three commuting, R-linearly independent locally nilpotent derivations of
the original four-variable ring, with exact common kernel C[F]. Every element
of this kernel, in particular any generator of it, fails to be a coordinate. -/
theorem commuting_derivations_dimension_four :
    ∃ d : Fin 3 → Derivation ℂ R R,
      (∀ i, d i (F + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent R d ∧
      (∀ p, (∀ i, d i p = 0) ↔ p ∈ Algebra.adjoin ℂ ({F} : Set R)) ∧
      (∀ g, (∀ i, d i g = 0) → ¬ ∃ (e : R ≃ₐ[ℂ] R) (j : Fin 4), e (X j) = g) := by
  simpa only [extendedF_four] using commuting_derivations_all_dimensions 4 (by decide)

end AbhyankarSathaye.CommutingDerivations

end

end OAI
