import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import OAI.AlgebraicGeometry.CommutingDerivations.ParameterBridge

namespace OAI

/-!
Explicit maps between the ambient localization and the polynomial algebra
over Laurent coefficients, using the unrestricted reconstruction formulas.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def ambientToFree : R →+* RelativePlane :=
  eval₂Hom (C.comp (algebraMap ℂ LaurentCoefficients))
    (ParameterBridge.values LaurentCoefficients coefficientC coefficientD)

@[simp] theorem ambientToFree_constant (a : ℂ) :
    ambientToFree (C a) = C (algebraMap ℂ LaurentCoefficients a) := by
  simp [ambientToFree]

@[simp] theorem ambientToFree_h :
    ambientToFree h = ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, h, ParameterBridge.values]
@[simp] theorem ambientToFree_u :
    ambientToFree u = ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, u, ParameterBridge.values]
@[simp] theorem ambientToFree_v :
    ambientToFree v = ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, v, ParameterBridge.values]
@[simp] theorem ambientToFree_w :
    ambientToFree w = ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, w, ParameterBridge.values]
@[simp] theorem ambientToFree_x : ambientToFree x = ParameterBridge.freeX LaurentCoefficients coefficientD := by
  simpa [x] using (ParameterBridge.free_relations _ _ _ coefficient_unit).1
@[simp] theorem ambientToFree_y : ambientToFree y = ParameterBridge.freeY LaurentCoefficients coefficientD := by
  simpa [y] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.1
@[simp] theorem ambientToFree_s : ambientToFree s = ParameterBridge.freeS LaurentCoefficients coefficientD := by
  simpa [s] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.2

@[simp] theorem ambientToFree_c : ambientToFree ambientC = C coefficientC := by
  simp [ambientC, F, p, ParameterBridge.freeH]

@[simp] theorem ambientToFree_shiftX : ambientToFree shiftX = X 0 := by
  simp [shiftX, ParameterBridge.freeX]
@[simp] theorem ambientToFree_shiftY : ambientToFree shiftY = X 1 := by
  simp [shiftY, ParameterBridge.freeY]

@[simp] theorem coefficientMap_complex (a : ℂ) :
    coefficientMap (algebraMap ℂ LaurentCoefficients a) = loc (C a) := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  change coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients (Polynomial.C a)) = _
  simp [coefficientMap, polynomialCoefficientMap, loc,
    IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]

def relativeForward : LocalizedAmbient →+* RelativePlane :=
  IsLocalization.Away.lift ambientC
    (show IsUnit (ambientToFree ambientC) by
      rw [ambientToFree_c]
      exact (IsUnit.of_mul_eq_one coefficientD coefficient_unit).map C)

@[simp] theorem relativeForward_loc (f : R) : relativeForward (loc f) = ambientToFree f := by
  simp [relativeForward, loc]

theorem relativeForward_coefficientMap :
    relativeForward.comp coefficientMap = (C : LaurentCoefficients →+* RelativePlane) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℂ))
  apply Polynomial.ringHom_ext
  · intro a
    simp [coefficientMap, polynomialCoefficientMap, relativeForward, ambientToFree,
      IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  · simp [coefficientMap, polynomialCoefficientMap, coefficientC]

@[simp] theorem relativeForward_coefficient (a : LaurentCoefficients) :
    relativeForward (coefficientMap a) = C a :=
  RingHom.congr_fun relativeForward_coefficientMap a

@[simp] theorem relativeForward_d : relativeForward localD = C coefficientD := by
  rw [← coefficientMap_D, relativeForward_coefficient]

@[simp] theorem relativeForward_alpha :
    relativeForward localAlpha = ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD := by
  simp [localAlpha, ParameterBridge.freeAlpha]
@[simp] theorem relativeForward_beta :
    relativeForward localBeta = ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD := by
  simp [localBeta, ParameterBridge.freeBeta]

@[simp] theorem relativeForward_shiftX : relativeForward (loc shiftX) = X 0 := by
  simp [shiftX, ParameterBridge.freeX]
@[simp] theorem relativeForward_shiftY : relativeForward (loc shiftY) = X 1 := by
  simp [shiftY, ParameterBridge.freeY]
@[simp] theorem relativeForward_T : relativeForward localT = X 2 := by
  simpa [localT, ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG] using
    (inverse_parameter
      (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeX LaurentCoefficients coefficientD)
      (ParameterBridge.freeY LaurentCoefficients coefficientD)
      (ParameterBridge.freeS LaurentCoefficients coefficientD)
      (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) (X 2 : RelativePlane)
      (ParameterBridge.free_bezout LaurentCoefficients coefficientC coefficientD coefficient_unit))

theorem relativeForward_backward :
    relativeForward.comp relativeBackward = RingHom.id RelativePlane := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [localCoordinates]

@[simp] theorem relativeBackward_freeS :
    relativeBackward (ParameterBridge.freeS LaurentCoefficients coefficientD) = loc s := by
  simpa [ParameterBridge.freeS, localCoordinates] using local_recover_s
@[simp] theorem relativeBackward_freeX :
    relativeBackward (ParameterBridge.freeX LaurentCoefficients coefficientD) = loc x := by
  simp [ParameterBridge.freeX, localCoordinates, shiftX]
@[simp] theorem relativeBackward_freeY :
    relativeBackward (ParameterBridge.freeY LaurentCoefficients coefficientD) = loc y := by
  simp [ParameterBridge.freeY, localCoordinates, shiftY]
@[simp] theorem relativeBackward_freeH :
    relativeBackward (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD) = loc h := by
  simpa [ParameterBridge.freeH] using local_section.symm
@[simp] theorem relativeBackward_freeAlpha :
    relativeBackward (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD) = localAlpha := by
  simp [ParameterBridge.freeAlpha, localAlpha]
@[simp] theorem relativeBackward_freeBeta :
    relativeBackward (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) = localBeta := by
  simp [ParameterBridge.freeBeta, localBeta]

theorem relativeBackward_free_original :
    relativeBackward (ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD) = loc u ∧
    relativeBackward (ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD) = loc v ∧
    relativeBackward (ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD) = loc w := by
  have hx : (loc u)^3 + loc h * loc v = loc x := by simp [x]
  have hy : -(loc u)^2 + loc h * loc w = loc y := by simp [y]
  have hs : S (loc h) (loc u) (loc v) (loc w) = loc s := by simp [s]
  simpa [ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG, localCoordinates, localT] using
    original_reconstruction (loc h) (loc x) (loc y) (loc s) localAlpha localBeta
      (loc u) (loc v) (loc w) local_bezout hx hy hs

theorem relativeBackward_forward :
    relativeBackward.comp relativeForward = RingHom.id LocalizedAmbient := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ambientC)
  apply MvPolynomial.ringHom_ext
  · intro a
    change relativeBackward (relativeForward (loc (C a))) = loc (C a)
    rw [relativeForward_loc, ambientToFree_constant, relativeBackward_C, coefficientMap_complex]
  · intro i
    obtain ⟨hu, hv, hw⟩ := relativeBackward_free_original
    change relativeBackward (relativeForward (loc (X i))) = loc (X i)
    fin_cases i
    · change relativeBackward (relativeForward (loc h)) = loc h
      rw [relativeForward_loc, ambientToFree_h]
      exact relativeBackward_freeH
    · change relativeBackward (relativeForward (loc u)) = loc u
      rw [relativeForward_loc, ambientToFree_u]
      exact hu
    · change relativeBackward (relativeForward (loc v)) = loc v
      rw [relativeForward_loc, ambientToFree_v]
      exact hv
    · change relativeBackward (relativeForward (loc w)) = loc w
      rw [relativeForward_loc, ambientToFree_w]
      exact hw

/-- Actual localized ring equivalence, with explicit maps and both composites. -/
def localizationRingEquiv : LocalizedAmbient ≃+* RelativePlane :=
  RingEquiv.ofRingHom relativeForward relativeBackward
    relativeForward_backward relativeBackward_forward

/-- The algebra structure is exactly the specified map c ↦ F+1. -/
@[instance_reducible]
def relativeAlgebra : Algebra LaurentCoefficients LocalizedAmbient := coefficientMap.toAlgebra

/-- Actual equivalence over the Laurent coefficient ring. -/
def localizationEquiv :
    letI := relativeAlgebra
    LocalizedAmbient ≃ₐ[LaurentCoefficients] RelativePlane :=
  letI := relativeAlgebra
  { localizationRingEquiv with
    commutes' := relativeForward_coefficient }

/-- The same explicit equivalence also preserves the original complex scalars. -/
def localizationComplexEquiv : LocalizedAmbient ≃ₐ[ℂ] RelativePlane :=
  { localizationRingEquiv with
    commutes' := by
      intro a
      change relativeForward (algebraMap ℂ LocalizedAmbient a) =
        algebraMap ℂ RelativePlane a
      rw [IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]
      change relativeForward (loc (C a)) = C (algebraMap ℂ LaurentCoefficients a)
      rw [relativeForward_loc, ambientToFree_constant] }

theorem relativeLocalizationContract_proved : RelativeLocalizationContract := by
  refine ⟨localizationRingEquiv, relativeForward_coefficient,
    relativeForward_shiftX, relativeForward_shiftY, relativeForward_T, ?_⟩
  rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI
