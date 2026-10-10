import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization
import OAI.AlgebraicGeometry.CommutingDerivations.LocalizedPartials

namespace OAI

/-!
Ordinary partial derivatives in the unused variables agree with the corresponding
localized coordinate derivatives and descend without a clearing factor.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem pderiv_sumAlgEquiv_symm {K I J : Type*} [CommRing K]
    (i : I) (p : MvPolynomial I (MvPolynomial J K)) :
    pderiv (Sum.inl i) ((sumAlgEquiv K I J).symm p) =
      (sumAlgEquiv K I J).symm (pderiv i p) := by
  apply (sumAlgEquiv K I J).injective
  simpa using (pderiv_sumAlgEquiv i ((sumAlgEquiv K I J).symm p)).symm

theorem splitAmbient_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    pderiv i (splitAmbient hn p) =
      splitAmbient hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  have he := pderiv_rename (blocksToAmbient hn).symm.injective
    (blocksToAmbient hn (Sum.inl i)) p
  simp only [Equiv.symm_apply_apply] at he
  change pderiv i
      (sumAlgEquiv ℂ (Fin (n-4)) (Fin 4) (rename (blocksToAmbient hn).symm p)) =
    sumAlgEquiv ℂ (Fin (n-4)) (Fin 4)
      (rename (blocksToAmbient hn).symm (pderiv (blocksToAmbient hn (Sum.inl i)) p))
  rw [pderiv_sumAlgEquiv, he]

theorem extendedLocMap_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    pderiv i (extendedLocMap hn p) =
      extendedLocMap hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  change pderiv i (MvPolynomial.map loc (splitAmbient hn p)) =
    MvPolynomial.map loc
      (splitAmbient hn (pderiv (blocksToAmbient hn (Sum.inl i)) p))
  rw [pderiv_map, splitAmbient_extra_pderiv]

theorem extendedLocalizationEquiv_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : ExtendedLocalizedAmbient n) :
    pderiv (blocksToOutput hn (Sum.inl i)) (extendedLocalizationEquiv hn p) =
      extendedLocalizationEquiv hn (pderiv i p) := by
  change pderiv (blocksToOutput hn (Sum.inl i))
      (rename (blocksToOutput hn)
        ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
          (MvPolynomial.map localizationComplexEquiv p))) =
    rename (blocksToOutput hn)
      ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
        (MvPolynomial.map localizationComplexEquiv (pderiv i p)))
  rw [pderiv_rename (blocksToOutput hn).injective, pderiv_sumAlgEquiv_symm, pderiv_map]

/-- The transported derivative indexed by an added coordinate agrees exactly
with the ordinary partial derivative in the full original n-variable ring. -/
theorem localized_extra_is_ordinary_partial {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    localizedPartial (extendedLocalizationEquiv hn) (blocksToOutput hn (Sum.inl i))
        (extendedLocMap hn p) =
      extendedLocMap hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  apply (extendedLocalizationEquiv hn).injective
  rw [localizedPartial_apply, AlgEquiv.apply_symm_apply,
    extendedLocalizationEquiv_extra_pderiv, extendedLocMap_extra_pderiv]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
