import OAI.RepresentationTheory.RestrictedTilting.SpecializeCompletion

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (I : Ideal R) (W : M →ₗ[R] (ι → R)) (Z : (ι → R) →ₗ[R] M) (a : R)
variable (hWZ : ∀ v, W (Z v) = a • v) (hZW : ∀ v, Z (W v) = a • v)

noncomputable def completedCoordinates : AdicCompletion I M →ₗ[AdicCompletion I R]
    (ι → AdicCompletion I R) :=
  (AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).toLinearMap ∘ₗ AdicCompletion.map I W

noncomputable def completedDenominator : (ι → AdicCompletion I R) →ₗ[AdicCompletion I R]
    AdicCompletion I M :=
  AdicCompletion.map I Z ∘ₗ (AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).symm.toLinearMap

lemma completedCoordinates_apply (v : AdicCompletion I M) (i : ι) :
    completedCoordinates I W v i = AdicCompletion.map I ((LinearMap.proj i).comp W) v := by
  change AdicCompletion.piEquivOfFintype I (fun _ : ι => R) (AdicCompletion.map I W v) i = _
  rw [AdicCompletion.piEquivOfFintype_apply]
  exact AdicCompletion.map_comp_apply I W (LinearMap.proj i) v

include hWZ in
lemma completedCoordinates_denominator (v : ι → AdicCompletion I R) :
    completedCoordinates I W (completedDenominator I Z v) =
      algebraMap R (AdicCompletion I R) a • v := by
  have he : W.comp Z = a • LinearMap.id := LinearMap.ext hWZ
  change AdicCompletion.piEquivOfFintype I (fun _ : ι => R)
    (AdicCompletion.map I W (AdicCompletion.map I Z
      ((AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).symm v))) = _
  rw [AdicCompletion.map_comp_apply, he, completion_map_scalar, map_smul,
    LinearEquiv.apply_symm_apply]

include hZW in
lemma completedDenominator_coordinates (v : AdicCompletion I M) :
    completedDenominator I Z (completedCoordinates I W v) =
      algebraMap R (AdicCompletion I R) a • v := by
  have he : Z.comp W = a • LinearMap.id := LinearMap.ext hZW
  change AdicCompletion.map I Z
    ((AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).symm
      ((AdicCompletion.piEquivOfFintype I (fun _ : ι => R)) (AdicCompletion.map I W v))) = _
  rw [LinearEquiv.symm_apply_apply, AdicCompletion.map_comp_apply, he, completion_map_scalar]

variable (L : Type*) [Field L] [Algebra (AdicCompletion I R) L]

noncomputable def completedCoordinatesEquiv
    (ha : algebraMap (AdicCompletion I R) L (algebraMap R (AdicCompletion I R) a) ≠ 0) :
    (L ⊗[AdicCompletion I R] AdicCompletion I M) ≃ₗ[L]
      (L ⊗[AdicCompletion I R] (ι → AdicCompletion I R)) :=
  specializedScalarEquiv (completedCoordinates I W) (completedDenominator I Z)
    (algebraMap R (AdicCompletion I R) a)
    (completedCoordinates_denominator I W Z a hWZ)
    (completedDenominator_coordinates I W Z a hZW) ha
end
end FiberFunctorProof

end OAI
