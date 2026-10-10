import OAI.AlgebraicGeometry.CommutingDerivations.Main
import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedExtraPartials
import OAI.AlgebraicGeometry.CommutingDerivations.MixedDescentFamily

namespace OAI

/-! The all-dimensional family may be chosen with the additional n-4
directions literally equal to the ordinary ambient coordinate partials. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def withOrdinaryExtras {n : ℕ} (hn : 4 ≤ n)
    (d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)) :
    Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  fun k => match (blocksToOutput hn).symm k with
    | Sum.inl i => pderiv (blocksToAmbient hn (Sum.inl i))
    | Sum.inr _ => d k

def extraClearingExponent {n : ℕ} (hn : 4 ≤ n) (N : ℕ) (k : Fin (n-1)) : ℕ :=
  match (blocksToOutput hn).symm k with
  | Sum.inl _ => 0
  | Sum.inr _ => N

theorem commuting_derivations_with_ordinary_extras (n : ℕ) (hn : 4 ≤ n) :
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) ∧
      (∀ i : Fin (n-4), d (blocksToOutput hn (Sum.inl i)) =
        pderiv (blocksToAmbient hn (Sum.inl i))) := by
  let := extendedAlgebra hn
  let := extendedScalarTower hn
  let := extended_isLocalization hn
  let : IsLocalization.Away (extendedAmbientParameter hn) (ExtendedLocalizedAmbient n) := by
    change IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n)
    exact extended_isLocalization hn
  let ι : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ExtendedLocalizedAmbient n := extendedLocAlgHom hn
  have hinj : Function.Injective ι :=
    extendedParameter_localization_injective hn (ExtendedLocalizedAmbient n)
  have hu : IsUnit (ι (extendedF hn+1)) :=
    IsLocalization.Away.algebraMap_isUnit (extendedF hn+1)
  obtain ⟨N, d, hdesc, _, _, _, _, _⟩ :=
    exists_commuting_family_of_localization (extendedF hn + 1) hinj
      (extendedLocalizationEquiv hn) coefficientC (extendedLocalizationEquiv_c hn)
      (Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)))
      (extended_localization_kernel_intersection hn)
  have hdesc' (k : Fin (n-1)) (p : MvPolynomial (Fin n) ℂ) :
      ι (withOrdinaryExtras hn d k p) =
        (ι (extendedF hn+1))^(extraClearingExponent hn N k) *
          localizedPartial (extendedLocalizationEquiv hn) k (ι p) := by
    obtain ⟨j, rfl⟩ := (blocksToOutput hn).surjective k
    cases j with
    | inl i =>
        simp only [withOrdinaryExtras, extraClearingExponent,
          Equiv.symm_apply_apply, pow_zero, one_mul]
        exact (localized_extra_is_ordinary_partial hn i p).symm
    | inr j =>
        simp only [withOrdinaryExtras, extraClearingExponent,
          Equiv.symm_apply_apply]
        exact hdesc (blocksToOutput hn (Sum.inr j)) p
  have hfrac (j : Fin (n-1)) : ∃ (m : ℕ) (r : MvPolynomial (Fin n) ℂ),
      (extendedLocalizationEquiv hn).symm (X j) * (ι (extendedF hn+1))^m = ι r :=
    IsLocalization.Away.surj (extendedF hn+1) ((extendedLocalizationEquiv hn).symm (X j))
  obtain ⟨hfix, hcomm, hnil, hind, hker⟩ :=
    family_properties_of_mixed_descent ι hinj (extendedF hn+1) hu
      (extendedLocalizationEquiv hn) coefficientC (extendedLocalizationEquiv_c hn)
      (extraClearingExponent hn N) (withOrdinaryExtras hn d) hdesc' hfrac
      (Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)))
      (extended_localization_kernel_intersection hn)
  refine ⟨withOrdinaryExtras hn d, hfix, hcomm, hnil, hind, hker, ?_, ?_⟩
  · intro g hg
    apply element_of_extendedF_subring_not_coordinate hn g
    have hmem := (hker g).mp hg
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq.symm⟩
  · intro i
    simp [withOrdinaryExtras]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
