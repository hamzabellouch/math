import Mathlib

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct
namespace ReverseLogKodaira.DifferentialBaseChange

section Linear
variable (A B M N : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

def alternatingRestriction (n : ℕ) : N [⋀^Fin n]→ₗ[A] (⋀[B]^n N) where
  toMultilinearMap := (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := (exteriorPower.ιMulti B n).map_eq_zero_of_eq

def exteriorScalarMap (f : M →ₗ[A] N) (n : ℕ) : (⋀[A]^n M) →ₗ[A] (⋀[B]^n N) :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestriction A B N n).compLinearMap f)

def tensorScalarMap (f : M →ₗ[A] N) (m : ℕ) : (⨂[A]^m M) →ₗ[A] (⨂[B]^m N) :=
  PiTensorProduct.lift (((PiTensorProduct.tprod B).restrictScalars A).compLinearMap
    fun _ : Fin m => f)

end Linear

section Differentials
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

abbrev Canonical (n : ℕ) := ⋀[A]^n (KaehlerDifferential R A)
abbrev Pluricanonical (n m : ℕ) := ⨂[A]^m (Canonical R A n)

def exteriorDifferentialMap (n : ℕ) : Canonical R A n →ₗ[A] Canonical S B n :=
  exteriorScalarMap A B _ _ (KaehlerDifferential.map R S A B) n

def pluricanonicalMap (n m : ℕ) : Pluricanonical R A n m →ₗ[A] Pluricanonical S B n m :=
  tensorScalarMap A B _ _ (exteriorDifferentialMap R S A B n) m

end Differentials

section LinearProofs
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

lemma lift_bijective_of_basis {I : Type*} (b : Module.Basis I A M)
    (c : Module.Basis I B N) (f : M →ₗ[A] N) (hf : ∀ i, f (b i) = c i) :
    Function.Bijective (f.liftBaseChange B) := by
  have he : f.liftBaseChange B = ((b.baseChange B).equiv c (Equiv.refl I)).toLinearMap := by
    apply (b.baseChange B).ext
    intro i
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    simp [Module.Basis.baseChange_apply, hf]
  rw [he]
  exact ((b.baseChange B).equiv c (Equiv.refl I)).bijective

@[simp] lemma exteriorScalarMap_wedge (f : M →ₗ[A] N) (n : ℕ) (v : Fin n → M) :
    exteriorScalarMap A B M N f n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (f ∘ v) := by
  simp only [exteriorScalarMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

lemma exterior_bijective_of_basis {I : Type*} [LinearOrder I]
    (b : Module.Basis I A M) (c : Module.Basis I B N)
    (f : M →ₗ[A] N) (hf : ∀ i, f (b i) = c i) (n : ℕ) :
    Function.Bijective ((exteriorScalarMap A B M N f n).liftBaseChange B) := by
  apply lift_bijective_of_basis (b.exteriorPower n) (c.exteriorPower n)
  intro i
  simp only [exteriorPower.coe_basis, exteriorPower.ιMulti_family, exteriorScalarMap_wedge]
  congr 1
  funext j
  exact hf _

lemma tensor_bijective_of_basis {I : Type*}
    (b : Module.Basis I A M) (c : Module.Basis I B N)
    (f : M →ₗ[A] N) (hf : ∀ i, f (b i) = c i) (m : ℕ) :
    Function.Bijective ((tensorScalarMap A B M N f m).liftBaseChange B) := by
  classical
  apply lift_bijective_of_basis (Basis.piTensorProduct fun _ : Fin m => b)
    (Basis.piTensorProduct fun _ : Fin m => c)
  intro i
  simp only [Basis.piTensorProduct_apply, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  change PiTensorProduct.tprod B (fun j => f (b (i j))) = PiTensorProduct.tprod B (fun j => c (i j))
  congr 1
  funext j
  exact hf _

end LinearProofs

section DifferentialProofs
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

lemma tensorKaehlerEquiv_tmul (b : B) (x : KaehlerDifferential R A) :
    KaehlerDifferential.tensorKaehlerEquiv R S A B (b ⊗ₜ[A] x) =
      b • KaehlerDifferential.map R S A B x := by
  have he : ((KaehlerDifferential.tensorKaehlerEquiv R S A B).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B (KaehlerDifferential R A) b) =
      b • KaehlerDifferential.map R S A B := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    simp
  exact LinearMap.congr_fun he x

 

theorem smooth_pluricanonical_baseChange
    [Algebra.IsStandardSmooth R A] (n m : ℕ) :
    Function.Bijective ((pluricanonicalMap R S A B n m).liftBaseChange B) := by
  classical
  let b := Module.Free.chooseBasis A (KaehlerDifferential R A)
  let : LinearOrder (Module.Free.ChooseBasisIndex A (KaehlerDifferential R A)) :=
    linearOrderOfSTO WellOrderingRel
  let c := (b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquiv R S A B)
  have hc (i) : KaehlerDifferential.map R S A B (b i) = c i := by
    simp [c, Module.Basis.baseChange_apply, tensorKaehlerEquiv_tmul]
  apply tensor_bijective_of_basis (b.exteriorPower n) (c.exteriorPower n)
  intro i
  simp only [exteriorDifferentialMap, exteriorPower.coe_basis, exteriorPower.ιMulti_family,
    exteriorScalarMap_wedge]
  congr 1
  funext j
  exact hc _

end DifferentialProofs

end ReverseLogKodaira.DifferentialBaseChange

end
end

end OAI
