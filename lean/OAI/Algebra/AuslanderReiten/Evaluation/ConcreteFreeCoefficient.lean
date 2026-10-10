import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreeCoordinateMap

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
private theorem threeValue {R : Type*} [Ring R] {U V W Z : ModuleCat R}
    {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ Z} {f : U ⟶ Z}
    {x : U} {y : V} {z : W} (hf : f = a ≫ b ≫ c)
    (ha : a x = y) (hb : b y = z) : f x = c z := by
  rw [hf, ModuleCat.comp_apply, ha, ModuleCat.comp_apply, hb]

private theorem identityValue {R : Type*} [Ring R] {U : ModuleCat R}
    {a : U ⟶ U} (h : a = 𝟙 U) (x : U) : a x = x := by
  rw [h, ModuleCat.id_apply]

private theorem comp_hom_apply {R : Type*} [Ring R] {U V W : ModuleCat R}
    (f : U ⟶ V) (g : V ⟶ W) (x : U) : (g.hom.comp f.hom) x = g (f x) := rfl

private theorem transferFunctionValue {U V : Type*} {f g : U → V}
    (hf : ∀ x, f x = g x) {x : U} {y : V} (h : g x = y) : f x = y :=
  (hf x).trans h

universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)
local notation "T₀" => T k q
local notation "S" => Resolution.Simple q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local instance (priority := 3000) coefficientNativeScalar : Module k (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).scalar
local instance (priority := 3000) coefficientNativeTower : IsScalarTower k (A k q) (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).tower

private theorem coefficientTensorValue (z : (D).term 0) (s t : S) :
    type_of% ((EnvelopingBimodule.coefficientComplexIso_tmul k (A k q)
      (nativeToCanonicalSimple q) (shuffledBarComplex q) 0 ⟨z⟩ (s ⊗ₜ[k] t)).trans
      (congrArg (fun (x : canonicalTensorSimple q) => BalancedTensor.tmul (k := k) (R := A k q)
        (⟨z⟩ : EnvelopingBimodule k (A k q) ((shuffledBarComplex q).X 0)) x)
        (ExternalTensor.canonicalTensorIso_inv_tmul k T₀ T₀ S S s t))) :=
  (EnvelopingBimodule.coefficientComplexIso_tmul k (A k q)
    (nativeToCanonicalSimple q) (shuffledBarComplex q) 0 ⟨z⟩ (s ⊗ₜ[k] t)).trans
    (congrArg (fun (x : canonicalTensorSimple q) => BalancedTensor.tmul (k := k) (R := A k q)
      (⟨z⟩ : EnvelopingBimodule k (A k q) ((shuffledBarComplex q).X 0)) x)
      (ExternalTensor.canonicalTensorIso_inv_tmul k T₀ T₀ S S s t))

private theorem freeTransferValue (z : (D).term 0) (s t : S) :
    type_of% (threeValue (evaluatedFreeCoordinate_eq q hq)
      (identityValue (simpleOrdinaryBarIso_f q 0) _) (coefficientTensorValue q z s t)) :=
  threeValue (evaluatedFreeCoordinate_eq q hq)
    (identityValue (simpleOrdinaryBarIso_f q 0) _) (coefficientTensorValue q z s t)

private theorem rawCoordinateValue
    (x : TwoCone.evaluatedRawTerm (k := k) (R := A k q) D hf (A.simpleFiniteModule q) 0) :
    freeCoordinateRaw q hq x = (evaluatedFreeCoordinate q hq) ((simpleResolutionTermIso q 0).inv x) :=
  comp_hom_apply (simpleResolutionTermIso q 0).inv (evaluatedFreeCoordinate q hq) x

private theorem rawCoordinateDirect
    (x : TwoCone.evaluatedRawTerm (k := k) (R := A k q) D hf (A.simpleFiniteModule q) 0) :
    freeCoordinateRaw q hq x = (evaluatedFreeCoordinate q hq) x := by
  rw [rawCoordinateValue]
  erw [simpleResolutionTermIso, TwoCone.evaluatedResolutionTermIso_inv_apply]

-- Specialize the equality of coordinate functions after computing the tensor value.
private theorem transferRawValues :
    type_of% (@transferFunctionValue _ _ _ _ (rawCoordinateDirect q hq)) :=
  @transferFunctionValue _ _ _ _ (rawCoordinateDirect q hq)

theorem freeCoordinateRaw_tmul_transfer (z : (D).term 0) (s t : S) :
    type_of% (transferRawValues q hq (freeTransferValue q hq z s t)) :=
  transferRawValues q hq (freeTransferValue q hq z s t)

end ArExplicit.T

end

end OAI
