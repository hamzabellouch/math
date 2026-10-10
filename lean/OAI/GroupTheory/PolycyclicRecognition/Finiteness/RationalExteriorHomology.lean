import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalRepresentationFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomologyNaturality

namespace OAI

/-! # Rational second homology surjects onto the rational exterior square -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def rationalUnit (M : Type) [AddCommGroup M] : M →ₗ[ℤ] ℚ ⊗[ℤ] M :=
  TensorProduct.mk ℤ ℚ M 1

theorem rationalUnit_span (M : Type) [AddCommGroup M] :
    Submodule.span ℚ (Set.range (rationalUnit M)) = ⊤ := by
  apply top_unique
  suffices h : ∀ x : ℚ ⊗[ℤ] M, x ∈ Submodule.span ℚ (Set.range (rationalUnit M)) by
    intro x _
    exact h x
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q m =>
    have h := (Submodule.span ℚ (Set.range (rationalUnit M))).smul_mem q
      (Submodule.subset_span ⟨m, rfl⟩)
    change q • ((1 : ℚ) ⊗ₜ[ℤ] m) ∈ Submodule.span ℚ (Set.range (rationalUnit M)) at h
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => exact Submodule.add_mem _ hx hy

def rationalExteriorValue {V : Type} [AddCommGroup V] [Module ℚ V]
    (x y : V) : ⋀[ℚ]^2 V := exteriorPower.ιMulti ℚ 2 ![x, y]

theorem rationalExteriorValue_swap {V : Type} [AddCommGroup V] [Module ℚ V] (x y : V) :
    rationalExteriorValue y x = -rationalExteriorValue x y := by
  have h := (exteriorPower.ιMulti ℚ 2 (M := V)).map_swap ![x, y]
    (i := 0) (j := 1) (by decide)
  have he : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext i
    fin_cases i <;> simp
  rw [he] at h
  exact h

theorem rationalExteriorValue_add_left {V : Type} [AddCommGroup V] [Module ℚ V]
    (x y z : V) : rationalExteriorValue (x + y) z =
      rationalExteriorValue x z + rationalExteriorValue y z :=
  (exteriorPower.ιMulti ℚ 2).map_vecCons_add ![z] x y

def rationalIntegralWedgePairing (M : Type) [AddCommGroup M] :
    M →+ M →+ ⋀[ℚ]^2 (ℚ ⊗[ℤ] M) where
  toFun x :=
    { toFun y := rationalExteriorValue (rationalUnit M x) (rationalUnit M y)
      map_zero' := by
        rw [map_zero]
        exact (exteriorPower.ιMulti ℚ 2).map_coord_zero (1 : Fin 2) rfl
      map_add' y z := by
        rw [map_add, rationalExteriorValue_swap,
          rationalExteriorValue_add_left,
          rationalExteriorValue_swap (rationalUnit M y),
          rationalExteriorValue_swap (rationalUnit M z)]
        abel }
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    change rationalExteriorValue (rationalUnit M 0) (rationalUnit M x) = 0
    rw [map_zero]
    exact (exteriorPower.ιMulti ℚ 2).map_coord_zero (0 : Fin 2) rfl
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    change rationalExteriorValue (rationalUnit M (x + y)) (rationalUnit M z) = _
    rw [map_add]
    exact (exteriorPower.ιMulti ℚ 2).map_vecCons_add _ _ _

def rationalLinearExtension {M V : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup V] [Module ℚ V]
    (f : M →ₗ[ℤ] V) : (ℚ ⊗[ℤ] M) →ₗ[ℚ] V :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight f)

@[simp] theorem rationalLinearExtension_tmul
    {M V : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module ℚ V]
    (f : M →ₗ[ℤ] V) (q : ℚ) (m : M) :
    rationalLinearExtension f (q ⊗ₜ[ℤ] m) = q • f m := rfl

def rationalAbelianH2Exterior (A : Type) [CommGroup A] :
    (ℚ ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A)) →ₗ[ℚ]
      ⋀[ℚ]^2 (ℚ ⊗[ℤ] Additive A) :=
  rationalLinearExtension (bilinearPairingHomology (rationalIntegralWedgePairing (Additive A)))

theorem rationalAbelianH2Exterior_class (a b : A) :
    rationalAbelianH2Exterior A ((1 / 2 : ℚ) ⊗ₜ[ℤ] abelianH2Class a b) =
      rationalExteriorValue (rationalUnit (Additive A) (Additive.ofMul a))
        (rationalUnit (Additive A) (Additive.ofMul b)) := by
  rw [rationalAbelianH2Exterior, rationalLinearExtension_tmul]
  have h := bilinearPairingHomology_antisymmetric
    (rationalIntegralWedgePairing (Additive A))
    (fun x y => rationalExteriorValue_swap (rationalUnit (Additive A) y)
      (rationalUnit (Additive A) x)) a b
  change bilinearPairingHomology (rationalIntegralWedgePairing (Additive A))
    (abelianH2Class a b) = (2 : ℤ) • _ at h
  rw [h]
  change (1 / 2 : ℚ) • ((2 : ℤ) • rationalExteriorValue _ _) = _
  rw [two_smul, ← two_smul ℚ, smul_smul]
  norm_num

theorem rationalAbelianH2Exterior_surjective (A : Type) [CommGroup A] :
    Function.Surjective (rationalAbelianH2Exterior A) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span ℚ 2 (ℚ ⊗[ℤ] Additive A)
    (rationalUnit_span (Additive A))]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := hv (Set.mem_range_self (0 : Fin 2))
  obtain ⟨b, hb⟩ := hv (Set.mem_range_self (1 : Fin 2))
  have he : v = ![rationalUnit (Additive A) a, rationalUnit (Additive A) b] := by
    funext i
    fin_cases i
    · exact ha.symm
    · exact hb.symm
  refine ⟨(1 / 2 : ℚ) ⊗ₜ[ℤ] abelianH2Class a.toMul b.toMul, ?_⟩
  rw [he]
  exact rationalAbelianH2Exterior_class a.toMul b.toMul

theorem rationalAbelianH2Exterior_natural {B : Type} [CommGroup B] (f : A →* B) :
    (rationalAbelianH2Exterior B).comp
        ((groupHomology.map f (integralTrivialCoefficientMap f) 2).hom.baseChange ℚ) =
      (exteriorPower.map 2 ((additiveGroupLinearMap f).baseChange ℚ)).comp
        (rationalAbelianH2Exterior A) := by
  let L := exteriorPower.map 2 ((additiveGroupLinearMap f).baseChange ℚ)
  have hp (a b : A) :
      L (rationalIntegralWedgePairing (Additive A) (Additive.ofMul a) (Additive.ofMul b)) =
        rationalIntegralWedgePairing (Additive B) (Additive.ofMul (f a)) (Additive.ofMul (f b)) := by
    change exteriorPower.map 2 ((additiveGroupLinearMap f).baseChange ℚ)
      (exteriorPower.ιMulti ℚ 2 ![rationalUnit (Additive A) (Additive.ofMul a),
        rationalUnit (Additive A) (Additive.ofMul b)]) =
      exteriorPower.ιMulti ℚ 2 ![rationalUnit (Additive B) (Additive.ofMul (f a)),
        rationalUnit (Additive B) (Additive.ofMul (f b))]
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  apply TensorProduct.AlgebraTensorModule.ext
  intro q z
  change q • bilinearPairingHomology (rationalIntegralWedgePairing (Additive B))
      (groupHomology.map f (integralTrivialCoefficientMap f) 2 z) =
    L (q • bilinearPairingHomology (rationalIntegralWedgePairing (Additive A)) z)
  rw [map_smul]
  apply congrArg (fun w => q • w)
  exact bilinearPairingHomology_natural f
    (rationalIntegralWedgePairing (Additive A)) (rationalIntegralWedgePairing (Additive B))
    (L.restrictScalars ℤ) hp z

end PolycyclicRecognition

end

end OAI
