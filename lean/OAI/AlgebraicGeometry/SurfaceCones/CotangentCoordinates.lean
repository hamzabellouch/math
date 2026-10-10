import Mathlib

namespace OAI

/-! Cotangent bases and Jacobians in the étale Kummer charts. -/
noncomputable section
open Algebra TensorProduct KaehlerDifferential Module

namespace CanonicalCoordinates
@[instance_reducible] def kaehlerModule (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] :
    Module A Ω[A⁄k] := inferInstance

@[instance_reducible] def exteriorSMul (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] : SMul A (ExteriorAlgebra A M) := inferInstance

variable {k B A : Type*} [CommRing k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  [Algebra.FormallyEtale B A]

/-- differentials of polynomial coordinates remain a basis after an
étale map. This is used below on the Kummer normalization chart. -/
def etaleBasis (e : MvPolynomial (Fin 2) k ≃ₐ[k] B) :
    Basis (Fin 2) A Ω[A⁄k] := by
  let C := MvPolynomial (Fin 2) k
  letI : Algebra C B := e.toRingHom.toAlgebra
  letI : Algebra C A := ((algebraMap B A).comp e.toRingHom).toAlgebra
  letI : IsScalarTower k C B :=
    IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap e.toAlgHom).symm
  letI : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k C A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IsScalarTower.algebraMap_apply k B A x).trans
      (congrArg (algebraMap B A) (e.commutes x)).symm)
  let eC : C ≃ₐ[C] B := { __ := e.toRingEquiv, commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale C B := Algebra.FormallyEtale.of_equiv eC
  letI : Algebra.FormallyEtale C A := Algebra.FormallyEtale.comp C B A
  exact ((KaehlerDifferential.mvPolynomialBasis k (Fin 2)).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k C A)

lemma etaleBasis_apply (e : MvPolynomial (Fin 2) k ≃ₐ[k] B) (i : Fin 2) :
    etaleBasis (A := A) e i =
      D k A (algebraMap B A (e (MvPolynomial.X i))) := by
  simp only [etaleBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- Jacobian of the local ramification coordinates in exterior
algebra. -/
lemma coordinateJacobian_seven {M : Type*} [AddCommGroup M] [Module A M] [Module k M]
    (d : Derivation k A M) (u v : A) :
    ExteriorAlgebra.ι A (d (u ^ 7)) *
      ExteriorAlgebra.ι A (d ((u * v) ^ 7)) =
    (49 * u ^ 13 * v ^ 6) •
      (ExteriorAlgebra.ι A (d u) * ExteriorAlgebra.ι A (d v)) := by
  simp only [Derivation.leibniz_pow, Derivation.leibniz, Nat.reduceSub,
    ← Nat.cast_smul_eq_nsmul A, smul_smul, map_smul, map_add, smul_add]
  simp only [mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    ExteriorAlgebra.ι_sq_zero, smul_zero, add_zero]
  congr 1
  ring

end CanonicalCoordinates

end

/-! Bases of the second exterior power of a rank-two module. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates

def topIndex : Set.powersetCard (Fin 2) 2 :=
  Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin 2)).toOrderEmbedding)

lemma topIndex_unique (s : Set.powersetCard (Fin 2) 2) : s = topIndex := by
  apply Subtype.ext
  have hs : s.val = Finset.univ := Finset.eq_univ_of_card s.val (by simp)
  have ht : topIndex.val = Finset.univ :=
    Finset.eq_univ_of_card topIndex.val (by simp)
  exact hs.trans ht.symm

def topIndexEquiv : Set.powersetCard (Fin 2) 2 ≃ Unit where
  toFun _ := ()
  invFun _ := topIndex
  left_inv s := (topIndex_unique s).symm
  right_inv _ := rfl

@[instance_reducible] def topModule (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] : Module A (⋀[A]^2 M) := inferInstance

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

def topBasis (b : Basis (Fin 2) A M) : Basis Unit A (⋀[A]^2 M) :=
  (b.exteriorPower 2).reindex topIndexEquiv

lemma topBasis_apply (b : Basis (Fin 2) A M) :
    topBasis b () = exteriorPower.ιMulti A 2 b := by
  rw [topBasis, Basis.reindex_apply, exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family]
  congr 1
  change b ∘ Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin 2)).toOrderEmbedding)) = b
  rw [Equiv.symm_apply_apply]
  rfl

lemma topBasis_coe (b : Basis (Fin 2) A M) :
    (topBasis b () : ExteriorAlgebra A M) =
      ExteriorAlgebra.ι A (b 0) * ExteriorAlgebra.ι A (b 1) := by
  rw [topBasis_apply]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

/-- Multiplying the wedge of a cotangent basis by an ring unit still
is a basis of the determinant line. -/
def unitTopBasis (b : Basis (Fin 2) A M) (u : Aˣ) : Basis Unit A (⋀[A]^2 M) :=
  (topBasis b).unitsSMul fun _ => u

lemma unitTopBasis_apply (b : Basis (Fin 2) A M) (u : Aˣ) :
    unitTopBasis b u () = (u : A) • exteriorPower.ιMulti A 2 b := by
  rw [unitTopBasis, Basis.unitsSMul_apply, topBasis_apply]
  rfl

end CanonicalCoordinates

end

/-! A rational top form and its regular canonical frame on the triple-point chart. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
@[instance_reducible] def exteriorMulAction (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] : MulAction A (ExteriorAlgebra A M) := inferInstance

variable (k A F : Type*) [CommRing k] [CommRing A] [CommRing F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

def exteriorMap : ExteriorAlgebra A Ω[A⁄k] →ₐ[A] ExteriorAlgebra F Ω[F⁄k] :=
  ExteriorAlgebra.lift A ⟨(ExteriorAlgebra.ι F).restrictScalars A ∘ₗ
    KaehlerDifferential.map k k A F, fun _m => ExteriorAlgebra.ι_sq_zero _⟩

lemma exteriorMap_D (a : A) :
    exteriorMap k A F (ExteriorAlgebra.ι A (D k A a)) =
      ExteriorAlgebra.ι F (D k F (algebraMap A F a)) := by
  erw [exteriorMap, ExteriorAlgebra.lift_ι_apply]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D]

/-- The rational cotangent basis induced from an affine étale coordinate
chart agrees with the differentials of those very same coordinates. -/
def rationalBasis [Algebra.FormallyEtale A F] (b : Basis (Fin 2) A Ω[A⁄k]) :
    Basis (Fin 2) F Ω[F⁄k] :=
  (b.baseChange F).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A F)

lemma rationalBasis_apply [Algebra.FormallyEtale A F]
    (b : Basis (Fin 2) A Ω[A⁄k]) (i : Fin 2) :
    rationalBasis k A F b i = KaehlerDifferential.map k k A F (b i) := by
  simp only [rationalBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]

lemma towerViaMiddle (k B A F : Type*) [CommRing k] [CommRing B] [CommRing A]
    [CommRing F] [Algebra k B] [Algebra k A] [Algebra k F] [Algebra B A]
    [Algebra B F] [Algebra A F] [IsScalarTower k B A] [IsScalarTower B A F]
    [IsScalarTower k B F] : IsScalarTower k A F :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq k B F,
      IsScalarTower.algebraMap_eq B A F, IsScalarTower.algebraMap_eq k B A]
    rfl)

lemma unitTopBasis_coe {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (b : Basis (Fin 2) A M) (u : Aˣ) :
    (unitTopBasis b u () : ExteriorAlgebra A M) =
      (u : A) • (ExteriorAlgebra.ι A (b 0) * ExteriorAlgebra.ι A (b 1)) := by
  rw [unitTopBasis, Basis.unitsSMul_apply]
  change (u : A) • (topBasis b () : ExteriorAlgebra A M) = _
  rw [topBasis_coe]

lemma exteriorMap_frame (b : Basis (Fin 2) A Ω[A⁄k]) (u : Aˣ)
    (coords : Fin 2 → A) (hcoords : ∀ i, b i = D k A (coords i)) :
    exteriorMap k A F (unitTopBasis b u () : ExteriorAlgebra A Ω[A⁄k]) =
      algebraMap A F (u : A) •
        (ExteriorAlgebra.ι F (D k F (algebraMap A F (coords 0))) *
          ExteriorAlgebra.ι F (D k F (algebraMap A F (coords 1)))) := by
  rw [unitTopBasis_coe, hcoords 0, hcoords 1, map_smul, map_mul,
    exteriorMap_D, exteriorMap_D, ← IsScalarTower.algebraMap_smul F]

end CanonicalCoordinates

end

end OAI
