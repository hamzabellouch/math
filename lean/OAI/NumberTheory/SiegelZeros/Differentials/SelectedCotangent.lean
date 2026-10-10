import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.JetCoefficients
import OAI.NumberTheory.SiegelZeros.Structure.IdentityHeight

namespace OAI

noncomputable section

namespace SiegelZeros

namespace WeightedTorusJets.W18

variable {K A S : Type*} [CommRing K] [CommRing A] [CommRing S]
variable [Algebra K A] [Algebra A S]

def derivationDualHom (D : Derivation K A A) : A →+* TrivSqZeroExt S S where
  toFun a := ⟨algebraMap A S a, algebraMap A S (D a)⟩
  map_one' := by ext <;> simp [D.map_one_eq_zero]
  map_zero' := by ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A S (a + b) = algebraMap A S a + algebraMap A S b
      exact map_add _ _ _
    · change algebraMap A S (D (a + b)) = algebraMap A S (D a) + algebraMap A S (D b)
      simp only [map_add]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A S (a * b) = algebraMap A S a * algebraMap A S b
      exact map_mul _ _ _
    · change algebraMap A S (D (a * b)) =
        algebraMap A S a * algebraMap A S (D b) +
          algebraMap A S (D a) * algebraMap A S b
      simp only [D.leibniz, smul_eq_mul, map_add, map_mul, mul_comm]

variable (M : Submonoid A) [IsLocalization M S]

def localizedDualHom (D : Derivation K A A) : S →+* TrivSqZeroExt S S :=
  IsLocalization.lift (M := M) (S := S) (g := derivationDualHom (S := S) D)
    (fun m : M => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsLocalization.map_units S m))

@[simp] theorem localizedDualHom_algebraMap (D : Derivation K A A) (a : A) :
    localizedDualHom (S := S) M D (algebraMap A S a) =
      ⟨algebraMap A S a, algebraMap A S (D a)⟩ :=
  IsLocalization.lift_eq _ a

@[simp] theorem localizedDualHom_fst (D : Derivation K A A) (s : S) :
    (localizedDualHom (S := S) M D s).fst = s := by
  have h : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (localizedDualHom M D) =
      RingHom.id S := by
    apply IsLocalization.ringHom_ext M
    ext a
    simp only [RingHom.comp_apply, RingHom.id_apply, localizedDualHom_algebraMap]
    rfl
  exact congrArg (fun f : S →+* S => f s) h

variable [Algebra K S] [IsScalarTower K A S]

@[simp] theorem localizedDualHom_scalar_snd (D : Derivation K A A) (k : K) :
    (localizedDualHom (S := S) M D (algebraMap K S k)).snd = 0 := by
  rw [IsScalarTower.algebraMap_apply K A S, localizedDualHom_algebraMap]
  simp

def localizedDerivation (D : Derivation K A A) : Derivation K S S where
  toFun s := (localizedDualHom (S := S) M D s).snd
  map_add' a b := by simp
  map_smul' k s := by
    rw [Algebra.smul_def, map_mul]
    simp [TrivSqZeroExt.snd_mul, Algebra.smul_def]
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp [TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm]

@[simp] theorem localizedDerivation_algebraMap (D : Derivation K A A) (a : A) :
    localizedDerivation (S := S) M D (algebraMap A S a) =
      algebraMap A S (D a) := by
  change (localizedDualHom M D (algebraMap A S a)).snd = _
  rw [localizedDualHom_algebraMap]
  rfl

theorem localizedDerivation_mk'_denominator (D : Derivation K A A) (a : A) (m : M) :
    algebraMap A S (m : A) *
        localizedDerivation M D (IsLocalization.mk' S a m) =
      algebraMap A S (D a) -
        IsLocalization.mk' S a m * algebraMap A S (D (m : A)) := by
  have h := congrArg (localizedDerivation (S := S) M D)
    (IsLocalization.mk'_spec' S a m)
  rw [(localizedDerivation M D).leibniz,
    localizedDerivation_algebraMap, localizedDerivation_algebraMap] at h
  simpa only [smul_eq_mul] using (eq_sub_iff_add_eq.mpr h)

theorem localizedDerivation_mk' (D : Derivation K A A) (a : A) (m : M) :
    localizedDerivation M D (IsLocalization.mk' S a m) =
      IsLocalization.mk' S (D a * (m : A) - a * D (m : A)) (m * m) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change localizedDerivation M D (IsLocalization.mk' S a m) *
    algebraMap A S ((m : A) * (m : A)) = _
  calc
    _ = (algebraMap A S (m : A) *
        localizedDerivation M D (IsLocalization.mk' S a m)) *
          algebraMap A S (m : A) := by rw [map_mul]; ac_rfl
    _ = (algebraMap A S (D a) - IsLocalization.mk' S a m *
        algebraMap A S (D (m : A))) * algebraMap A S (m : A) := by
          rw [localizedDerivation_mk'_denominator]
    _ = algebraMap A S (D a) * algebraMap A S (m : A) -
        (IsLocalization.mk' S a m * algebraMap A S (m : A)) *
          algebraMap A S (D (m : A)) := by
            rw [sub_mul]
            congr 1
            ac_rfl
    _ = _ := by rw [IsLocalization.mk'_spec]; simp only [map_sub, map_mul]

include M in
omit [Algebra K A] [IsScalarTower K A S] in
theorem localization_derivation_ext (D E : Derivation K S S)
    (h : ∀ a : A, D (algebraMap A S a) = E (algebraMap A S a)) : D = E := by
  apply Derivation.ext
  intro s
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M s
  apply (IsLocalization.map_units S m).mul_left_cancel
  have hD := congrArg D (IsLocalization.mk'_spec' S a m)
  have hE := congrArg E (IsLocalization.mk'_spec' S a m)
  rw [D.leibniz] at hD
  rw [E.leibniz] at hE
  simp only [smul_eq_mul, h] at hD hE
  exact add_right_cancel (hD.trans hE.symm)

theorem localizedDerivation_commute (D E : Derivation K A A)
    (h : Function.Commute D E) :
    Function.Commute (localizedDerivation (S := S) M D)
      (localizedDerivation (S := S) M E) := by
  have hz : ⁅localizedDerivation (S := S) M D, localizedDerivation (S := S) M E⁆ =
      (0 : Derivation K S S) := by
    apply localization_derivation_ext M
    intro a
    simp only [Derivation.commutator_apply, localizedDerivation_algebraMap,
      Derivation.zero_apply]
    rw [h a, sub_self]
  intro s
  have hs := congrArg (fun d : Derivation K S S => d s) hz
  exact sub_eq_zero.mp hs

end WeightedTorusJets.W18

namespace W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

theorem ideal_smul_quotient_zero (x : I) (z : R ⧸ I) : (x : R) • z = 0 := by
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk I (x : R) * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

def normalRestriction : I →ₗ[R] R ⧸ I where
  toFun x := D x
  map_add' x y := D.map_add x y
  map_smul' r x := by
    change D (r * (x : R)) = r • D (x : R)
    rw [D.leibniz, ideal_smul_quotient_zero I x, add_zero]

theorem normalRestriction_product_zero (x y : I) : normalRestriction I D (x * y) = 0 := by
  change D ((x : R) * (y : R)) = 0
  rw [D.leibniz, ideal_smul_quotient_zero I x, ideal_smul_quotient_zero I y, add_zero]

def conormalPairing : I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (normalRestriction I D) (normalRestriction_product_zero I D)

@[simp] theorem conormalPairing_toCotangent (x : I) :
    conormalPairing I D (I.toCotangent x) = D x := rfl

instance cotangentQuotientScalarTower : IsScalarTower R (R ⧸ I) I.Cotangent := by
  infer_instance

def residueConormalPairing : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (conormalPairing I D).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

@[simp] theorem residueConormalPairing_apply (x : I.Cotangent) :
    residueConormalPairing I D x = conormalPairing I D x := rfl

@[simp] theorem residueConormalPairing_toCotangent (x : I) :
    residueConormalPairing I D (I.toCotangent x) = D x := rfl

theorem residueConormalPairing_restrictScalars :
    (residueConormalPairing I D).restrictScalars R = conormalPairing I D := by
  ext x
  rfl

def reducedDerivation (D₀ : Derivation K R R) : Derivation K R (R ⧸ I) :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.compDer D₀

@[simp] theorem reducedDerivation_apply (D₀ : Derivation K R R) (x : R) :
    reducedDerivation I D₀ x = Ideal.Quotient.mk I (D₀ x) := rfl

def derivationNormal (D₀ : Derivation K R R) : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  residueConormalPairing I (reducedDerivation I D₀)

@[simp] theorem derivationNormal_toCotangent (D₀ : Derivation K R R) (x : I) :
    derivationNormal I D₀ (I.toCotangent x) = Ideal.Quotient.mk I (D₀ x) := rfl

end W58

namespace WeightedTorusJets.W18

open _root_.OAI.SiegelZeros.W58

variable (K : Type*) [Field K]

def torusDerivation (v : Fin 4 → K) :
    Derivation K (TorusRing K) (TorusRing K) :=
  localizedDerivation (Submonoid.powers (coordinateProduct K)) (invariantDerivation v)

@[simp] theorem torusDerivation_polynomial (v : Fin 4 → K) (f : AmbientPolynomial K) :
    torusDerivation K v (algebraMap (AmbientPolynomial K) (TorusRing K) f) =
      algebraMap (AmbientPolynomial K) (TorusRing K) (invariantDerivation v f) :=
  localizedDerivation_algebraMap _ _ _

theorem torusDerivation_commute (v w : Fin 4 → K) :
    Function.Commute (torusDerivation K v) (torusDerivation K w) :=
  localizedDerivation_commute _ _ _ (W19.invariantDerivation_commute v w)

@[reducible] instance (priority := 1100) genericLocalRingSelfModule
    (p : Ideal (TorusRing K)) [p.IsPrime] :
    Module (GenericLocalRing K p) (GenericLocalRing K p) :=
  Semiring.toModule

def localTorusDerivation (p : Ideal (TorusRing K)) [p.IsPrime] (v : Fin 4 → K) :
    Derivation K (GenericLocalRing K p) (GenericLocalRing K p) :=
  localizedDerivation (K := K) (A := TorusRing K) (S := GenericLocalRing K p)
    p.primeCompl (torusDerivation K v)

@[simp] theorem localTorusDerivation_algebraMap (p : Ideal (TorusRing K)) [p.IsPrime]
    (v : Fin 4 → K) (f : TorusRing K) :
    localTorusDerivation K p v (algebraMap (TorusRing K) (GenericLocalRing K p) f) =
      algebraMap (TorusRing K) (GenericLocalRing K p) (torusDerivation K v f) :=
  localizedDerivation_algebraMap (K := K) (A := TorusRing K)
    (S := GenericLocalRing K p) p.primeCompl (torusDerivation K v) f

theorem localTorusDerivation_commute (p : Ideal (TorusRing K)) [p.IsPrime]
    (v w : Fin 4 → K) :
    Function.Commute (localTorusDerivation K p v) (localTorusDerivation K p w) :=
  localizedDerivation_commute (K := K) (A := TorusRing K)
    (S := GenericLocalRing K p) p.primeCompl (torusDerivation K v)
      (torusDerivation K w) (torusDerivation_commute K v w)

theorem localTorusDerivation_polynomial (p : Ideal (TorusRing K)) [p.IsPrime]
    (v : Fin 4 → K) (f : AmbientPolynomial K) :
    localTorusDerivation K p v
        (algebraMap (TorusRing K) (GenericLocalRing K p)
          (algebraMap (AmbientPolynomial K) (TorusRing K) f)) =
      algebraMap (TorusRing K) (GenericLocalRing K p)
        (algebraMap (AmbientPolynomial K) (TorusRing K) (invariantDerivation v f)) := by
  rw [localTorusDerivation_algebraMap, torusDerivation_polynomial]

theorem localTorusDerivation_quotient (p : Ideal (TorusRing K)) [p.IsPrime]
    (v : Fin 4 → K) (f : TorusRing K) (s : p.primeCompl) :
    algebraMap (TorusRing K) (GenericLocalRing K p) (s : TorusRing K) *
        localTorusDerivation K p v (IsLocalization.mk' (GenericLocalRing K p) f s) =
      algebraMap (TorusRing K) (GenericLocalRing K p) (torusDerivation K v f) -
        IsLocalization.mk' (GenericLocalRing K p) f s *
          algebraMap (TorusRing K) (GenericLocalRing K p)
            (torusDerivation K v (s : TorusRing K)) :=
  localizedDerivation_mk'_denominator (K := K) (A := TorusRing K)
    (S := GenericLocalRing K p) p.primeCompl (torusDerivation K v) f s

end WeightedTorusJets.W18

namespace WeightedTorusJets.IdentityCotangentRank
open _root_.OAI.SiegelZeros.W58

variable (K : Type*) [Field K]

abbrev LocalRing := IdentityLocalRing K

@[reducible] local instance localRingCommSemiring : CommSemiring (LocalRing K) :=
  (inferInstance : CommRing (LocalRing K)).toCommSemiring

abbrev Residue := IsLocalRing.ResidueField (LocalRing K)
abbrev Maximal := IsLocalRing.maximalIdeal (LocalRing K)
abbrev Cotangent := IsLocalRing.CotangentSpace (LocalRing K)

@[reducible] local instance residueSelfModule : Module (Residue K) (Residue K) :=
  Semiring.toModule

@[reducible] local instance residueDualModule :
    Module (Residue K) (Cotangent K →ₗ[Residue K] Residue K) :=
  LinearMap.module

def identityResidueEquiv : Residue K ≃+* K :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (identityIdeal K) (LocalRing K)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (identityEvaluation_surjective K))

@[simp] theorem identityResidueEquiv_base (f : TorusRing K) :
    identityResidueEquiv K
      (IsLocalRing.residue (LocalRing K) (algebraMap (TorusRing K) (LocalRing K) f)) =
        identityEvaluation K f := by
  exact congrArg
    (RingHom.quotientKerEquivOfSurjective (identityEvaluation_surjective K))
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal (identityIdeal K) (LocalRing K)).symm_apply_apply
      (Ideal.Quotient.mk (identityIdeal K) f))

@[simp] theorem identityResidueEquiv_scalar (a : K) :
    identityResidueEquiv K (algebraMap K (Residue K) a) = a := by
  change identityResidueEquiv K
    (IsLocalRing.residue (LocalRing K) (algebraMap K (LocalRing K) a)) = a
  rw [IsScalarTower.algebraMap_apply K (TorusRing K) (LocalRing K)]
  change identityResidueEquiv K
    (IsLocalRing.residue (LocalRing K)
      (algebraMap (TorusRing K) (LocalRing K) (algebraMap K (TorusRing K) a))) = a
  rw [identityResidueEquiv_base]
  change identityEvaluation K
    (algebraMap (AmbientPolynomial K) (TorusRing K) (MvPolynomial.C a)) = a
  simp

def identityResidueAlgEquiv : Residue K ≃ₐ[K] K :=
  { identityResidueEquiv K with commutes' := identityResidueEquiv_scalar K }

def localCoordinateDifference (i : Fin 4) : LocalRing K :=
  algebraMap (TorusRing K) (LocalRing K) (coordinate K i) - 1

theorem localCoordinateDifference_mem (i : Fin 4) :
    localCoordinateDifference K i ∈ Maximal K := by
  have h := Ideal.mem_map_of_mem (algebraMap (TorusRing K) (LocalRing K))
    (coordinate_sub_one_mem_identityIdeal K i)
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal (identityIdeal K) (LocalRing K)] at h
  have he : algebraMap (TorusRing K) (LocalRing K) (coordinate K i - 1) =
      localCoordinateDifference K i := by
    apply eq_sub_iff_add_eq.mpr
    have he := (algebraMap (TorusRing K) (LocalRing K)).map_add
      (coordinate K i - 1) 1
    simpa only [sub_add_cancel, map_one] using he.symm
  exact he ▸ h

def coordinateClass (i : Fin 4) : Cotangent K :=
  (Maximal K).toCotangent ⟨localCoordinateDifference K i,
    localCoordinateDifference_mem K i⟩

theorem identityIdeal_span :
    Ideal.span (Set.range (fun i : Fin 4 => coordinate K i - 1)) = identityIdeal K := by
  let S : Ideal (TorusRing K) :=
    Ideal.span (Set.range (fun i : Fin 4 => coordinate K i - 1))
  have hS : S ≤ identityIdeal K := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact coordinate_sub_one_mem_identityIdeal K i
  have hcoord (i : Fin 4) : Ideal.Quotient.mk S (coordinate K i) = 1 := by
    have hz : Ideal.Quotient.mk S (coordinate K i - 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span ⟨i, rfl⟩)
    have he := (Ideal.Quotient.mk S).map_add (coordinate K i - 1) 1
    simpa only [sub_add_cancel, hz, map_one, zero_add] using he
  have heq : Ideal.Quotient.mk S =
      (algebraMap K (TorusRing K ⧸ S)).comp (identityEvaluation K) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinateProduct K))
    apply MvPolynomial.ringHom_ext
    · intro a
      change algebraMap (AmbientPolynomial K) (TorusRing K ⧸ S) (MvPolynomial.C a) =
        algebraMap K (TorusRing K ⧸ S)
          (identityEvaluation K (algebraMap (AmbientPolynomial K) (TorusRing K)
            (MvPolynomial.C a)))
      simpa only [identityEvaluation_polynomial, MvPolynomial.eval_C,
        MvPolynomial.algebraMap_eq] using
        (IsScalarTower.algebraMap_apply K (AmbientPolynomial K) (TorusRing K ⧸ S) a).symm
    · intro i
      change Ideal.Quotient.mk S (coordinate K i) =
        algebraMap K (TorusRing K ⧸ S) (identityEvaluation K (coordinate K i))
      simp [hcoord]
  apply le_antisymm hS
  intro f hf
  rw [← Ideal.Quotient.eq_zero_iff_mem, heq]
  change algebraMap K (TorusRing K ⧸ S) (identityEvaluation K f) = 0
  rw [mem_identityIdeal] at hf
  rw [hf, map_zero]

theorem maximal_span :
    Ideal.span (Set.range (localCoordinateDifference K)) = Maximal K := by
  change Ideal.span (Set.range (localCoordinateDifference K)) =
    IsLocalRing.maximalIdeal (LocalRing K)
  have hm := congrArg
    (Ideal.map (algebraMap (TorusRing K) (LocalRing K))) (identityIdeal_span K)
  rw [Ideal.map_span] at hm
  have hcoord (i : Fin 4) :
      algebraMap (TorusRing K) (LocalRing K) (coordinate K i - 1) =
        localCoordinateDifference K i := by
    apply eq_sub_iff_add_eq.mpr
    have he := (algebraMap (TorusRing K) (LocalRing K)).map_add
      (coordinate K i - 1) 1
    simpa only [sub_add_cancel, map_one] using he.symm
  have hr : (algebraMap (TorusRing K) (LocalRing K)) ''
      Set.range (fun i : Fin 4 => coordinate K i - 1) =
        Set.range (localCoordinateDifference K) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hcoord i
  rw [hr] at hm
  exact hm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal
    (identityIdeal K) (LocalRing K))

theorem coordinateClass_span :
    Submodule.span (Residue K) (Set.range (coordinateClass K)) = ⊤ := by
  have hgen : Submodule.span (LocalRing K)
      (Set.range (fun i : Fin 4 => (⟨localCoordinateDifference K i,
        localCoordinateDifference_mem K i⟩ : Maximal K))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _ (localCoordinateDifference_mem K)).mpr
      (maximal_span K)
  convert (IsLocalRing.CotangentSpace.span_image_eq_top_iff).mpr hgen using 1
  rw [← Set.range_comp]
  rfl

def invariantNormal (v : Fin 4 → K) : Cotangent K →ₗ[Residue K] Residue K :=
  SiegelZeros.W58.derivationNormal (Maximal K)
    (W18.localTorusDerivation K (identityIdeal K) v)

lemma invariantDerivation_X (v : Fin 4 → K) (j : Fin 4) :
    W18.invariantDerivation v (MvPolynomial.X j) =
      MvPolynomial.C (v j) * MvPolynomial.X j := by
  classical
  rw [W18.invariantDerivation_apply]
  rw [Finset.sum_eq_single j]
  · rw [MvPolynomial.pderiv_X_self, mul_one]
  · intro i _ hij
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), mul_zero, mul_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem local_derivative_coordinate (v : Fin 4 → K) (j : Fin 4) :
    W18.localTorusDerivation K (identityIdeal K) v (localCoordinateDifference K j) =
      algebraMap K (LocalRing K) (v j) *
        algebraMap (TorusRing K) (LocalRing K) (coordinate K j) := by
  let D := W18.localTorusDerivation K (identityIdeal K) v
  change D (algebraMap (TorusRing K) (LocalRing K) (coordinate K j) - 1) = _
  have hD : D (algebraMap (TorusRing K) (LocalRing K) (coordinate K j) - 1) =
      D (algebraMap (TorusRing K) (LocalRing K) (coordinate K j)) := by
    have he := D.map_add
      (algebraMap (TorusRing K) (LocalRing K) (coordinate K j) - 1) 1
    have hOne : D 1 = 0 := D.map_one_eq_zero'
    simpa only [sub_add_cancel, hOne, add_zero] using he.symm
  rw [hD]
  change W18.localTorusDerivation K (identityIdeal K) v
    (algebraMap (TorusRing K) (LocalRing K) (coordinate K j)) = _
  rw [W18.localTorusDerivation_algebraMap]
  change algebraMap (TorusRing K) (LocalRing K)
    (W18.torusDerivation K v
      (algebraMap (AmbientPolynomial K) (TorusRing K) (MvPolynomial.X j))) = _
  rw [W18.torusDerivation_polynomial, invariantDerivation_X,
    (algebraMap (AmbientPolynomial K) (TorusRing K)).map_mul,
    (algebraMap (TorusRing K) (LocalRing K)).map_mul]
  congr 1

theorem residue_coordinate (j : Fin 4) :
    IsLocalRing.residue (LocalRing K)
      (algebraMap (TorusRing K) (LocalRing K) (coordinate K j)) = 1 := by
  have h : IsLocalRing.residue (LocalRing K) (localCoordinateDifference K j) = 0 :=
    (IsLocalRing.residue_eq_zero_iff (localCoordinateDifference K j)).mpr
      (localCoordinateDifference_mem K j)
  change IsLocalRing.residue (LocalRing K)
    (algebraMap (TorusRing K) (LocalRing K) (coordinate K j) - 1) = 0 at h
  have he := (IsLocalRing.residue (LocalRing K)).map_add
    (algebraMap (TorusRing K) (LocalRing K) (coordinate K j) - 1) 1
  simpa only [sub_add_cancel, h, map_one, zero_add] using he

theorem invariantNormal_coordinateClass (v : Fin 4 → K) (j : Fin 4) :
    invariantNormal K v (coordinateClass K j) = algebraMap K (Residue K) (v j) := by
  change IsLocalRing.residue (LocalRing K)
    (W18.localTorusDerivation K (identityIdeal K) v (localCoordinateDifference K j)) = _
  rw [local_derivative_coordinate, (IsLocalRing.residue (LocalRing K)).map_mul,
    residue_coordinate, mul_one]
  rfl

theorem coordinate_normal_pairing (i j : Fin 4) :
    invariantNormal K (Pi.single i 1) (coordinateClass K j) =
      if j = i then 1 else 0 := by
  classical
  rw [invariantNormal_coordinateClass]
  by_cases h : j = i <;> simp [h]

theorem coordinateClass_linearIndependent :
    LinearIndependent (Residue K) (coordinateClass K) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have h := congrArg (invariantNormal K (Pi.single j 1)) ha
  simpa [map_sum, map_smul, coordinate_normal_pairing] using h

def coordinateCotangentBasis : Module.Basis (Fin 4) (Residue K) (Cotangent K) :=
  Module.Basis.mk (coordinateClass_linearIndependent K)
    (le_of_eq (coordinateClass_span K).symm)

@[simp] theorem coordinateCotangentBasis_apply (j : Fin 4) :
    coordinateCotangentBasis K j = coordinateClass K j :=
  Module.Basis.mk_apply _ _ j

theorem identity_cotangent_finrank : Module.finrank (Residue K) (Cotangent K) = 4 := by
  simpa using Module.finrank_eq_card_basis (coordinateCotangentBasis K)

theorem invariantNormal_linearIndependent {ι : Type*} [Fintype ι]
    (v : ι → Fin 4 → K) (hv : LinearIndependent K v) :
    LinearIndependent (Residue K) (fun i => invariantNormal K (v i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hvzero : ∑ k, (identityResidueEquiv K (a k)) • v k = 0 := by
    funext j
    have hj := congrArg
      (fun f : Cotangent K →ₗ[Residue K] Residue K => f (coordinateClass K j)) ha
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      invariantNormal_coordinateClass] at hj
    change (∑ k, a k * algebraMap K (Residue K) (v k j)) = 0 at hj
    have h := congrArg (identityResidueEquiv K) hj
    simpa only [map_sum, map_mul, identityResidueEquiv_scalar, map_zero,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hai := Fintype.linearIndependent_iff.mp hv
    (fun k => identityResidueEquiv K (a k)) hvzero i
  apply (identityResidueEquiv K).injective
  simpa using hai

theorem invariant_three_normal_rank (v : Fin 3 → Fin 4 → K)
    (hv : LinearIndependent K v) :
    Module.finrank (Residue K)
      (Submodule.span (Residue K) (Set.range (fun i => invariantNormal K (v i)))) = 3 := by
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (invariantNormal_linearIndependent K v hv)

end WeightedTorusJets.IdentityCotangentRank

namespace Result.Workers.W57

section
variable (K : Type*) [CommRing K]

def rectangleFirst (a b c : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c) :
    Fin 3 → RectangleJet K a b c →+ K
  | 0 => rectangleCoeff K a b c 1 0 0 ha (lt_trans Nat.zero_lt_one hb)
      (lt_trans Nat.zero_lt_one hc)
  | 1 => rectangleCoeff K a b c 0 1 0 (lt_trans Nat.zero_lt_one ha) hb
      (lt_trans Nat.zero_lt_one hc)
  | 2 => rectangleCoeff K a b c 0 0 1 (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) hc

private theorem projection_surjective (a b c : ℕ) :
    Function.Surjective (rectangleProjection K a b c) := by
  apply Function.Surjective.comp
    (Ideal.Quotient.mk_surjective :
      Function.Surjective (jetProjection (Jet (Jet K c) b) a))
  apply Function.Surjective.comp
    (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)
  exact PowerSeries.map_surjective _
    (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)

theorem rectangleFirst_mul (a b c : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c)
    (j : Fin 3) (x y : RectangleJet K a b c) :
    rectangleFirst K a b c ha hb hc j (x*y) =
      rectangleResidue K a b c (lt_trans Nat.zero_lt_one ha)
        (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc) x *
        rectangleFirst K a b c ha hb hc j y +
      rectangleResidue K a b c (lt_trans Nat.zero_lt_one ha)
        (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc) y *
        rectangleFirst K a b c ha hb hc j x := by
  obtain ⟨f, rfl⟩ := projection_surjective K a b c x
  obtain ⟨g, rfl⟩ := projection_surjective K a b c y
  rw [← map_mul]
  fin_cases j <;>
    simp only [rectangleFirst, rectangleCoeff_projection, rectangleResidue_projection] <;>
    simp only [PowerSeries.coeff_one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_add, map_mul] <;> ring

variable [Algebra ℚ K]

def augmentationFirst (a b c : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c) (j : Fin 3) :
    rectangleAugmentation K a b c (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc) →ₗ[ℚ] K :=
  (rectangleFirst K a b c ha hb hc j).toRatLinearMap.comp
    ((rectangleAugmentation K a b c (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc)).restrictScalars ℚ).subtype

theorem augmentationFirst_product_zero (a b c : ℕ)
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (j : Fin 3)
    (x y : rectangleAugmentation K a b c (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc)) :
    augmentationFirst K a b c ha hb hc j (x*y) = 0 := by
  change rectangleFirst K a b c ha hb hc j ((x : RectangleJet K a b c) * y) = 0
  rw [rectangleFirst_mul]
  have hx := x.property
  have hy := y.property
  change rectangleResidue K a b c _ _ _ x = 0 at hx
  change rectangleResidue K a b c _ _ _ y = 0 at hy
  rw [hx, hy, zero_mul, zero_mul, add_zero]

def augmentationCotangentCoefficient (a b c : ℕ)
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (j : Fin 3) :
    (rectangleAugmentation K a b c (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc)).Cotangent →ₗ[ℚ] K :=
  Ideal.Cotangent.lift (augmentationFirst K a b c ha hb hc j)
    (augmentationFirst_product_zero K a b c ha hb hc j)

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem rectangleFirst_taylor (D : Fin 3 → Derivation ℚ R R) (ρ : R →+* K)
    (a b c : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c) (j : Fin 3) (f : R) :
    rectangleFirst K a b c ha hb hc j
      (rectangularJetHom K (D 0) (D 1) (D 2) ρ a b c f) = ρ (D j f) := by
  fin_cases j <;> simp [rectangleFirst, rectangleCoeff_taylor]

def rectangularJetAlgHom (D : Fin 3 → Derivation ℚ R R) (ρ : R →+* K)
    (a b c : ℕ) : R →ₐ[ℚ] RectangleJet K a b c where
  __ := rectangularJetHom K (D 0) (D 1) (D 2) ρ a b c
  commutes' q := RingHom.map_rat_algebraMap _ q

theorem quotientTaylor_augmentation_comap (I : Ideal R)
    (D : Fin 3 → Derivation ℚ R R) (a b c : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    (rectangleAugmentation (R ⧸ I) a b c ha hb hc).comap
      (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) a b c) = I := by
  ext f
  change rectangleResidue (R ⧸ I) a b c ha hb hc
    (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) a b c f) = 0 ↔ _
  rw [rectangleResidue_taylor, Ideal.Quotient.eq_zero_iff_mem]

def sourceTaylorCotangent (I : Ideal R) (D : Fin 3 → Derivation ℚ R R)
    (a b c : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c) :
    I.Cotangent →ₗ[ℚ]
      (rectangleAugmentation (R ⧸ I) a b c (lt_trans Nat.zero_lt_one ha)
        (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc)).Cotangent :=
  Ideal.mapCotangent I
    (rectangleAugmentation (R ⧸ I) a b c (lt_trans Nat.zero_lt_one ha)
      (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc))
    (rectangularJetAlgHom (R ⧸ I) D (Ideal.Quotient.mk I) a b c)
    (by
      change I ≤ (rectangleAugmentation (R ⧸ I) a b c _ _ _).comap
        (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) a b c)
      rw [quotientTaylor_augmentation_comap])

theorem sourceTaylorCotangent_coefficient (I : Ideal R)
    (D : Fin 3 → Derivation ℚ R R) (a b c : ℕ)
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (j : Fin 3) (z : I.Cotangent) :
    augmentationCotangentCoefficient (R ⧸ I) a b c ha hb hc j
      (sourceTaylorCotangent I D a b c ha hb hc z) =
      SiegelZeros.W58.derivationNormal I (D j) z := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  change rectangleFirst (R ⧸ I) a b c ha hb hc j
    (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) a b c x) =
      Ideal.Quotient.mk I (D j x)
  exact rectangleFirst_taylor (R ⧸ I) D (Ideal.Quotient.mk I) a b c ha hb hc j x

end

variable (K : Type*) [CommRing K]

def selectedFirst (t : Fin 3 → ℕ) (ht : ∀ j, 0 < t j) :
    (j : Fin 3) → 1 < t j → RectangleJet K (t 0) (t 1) (t 2) →+ K
  | 0, hj => rectangleCoeff K (t 0) (t 1) (t 2) 1 0 0 hj (ht 1) (ht 2)
  | 1, hj => rectangleCoeff K (t 0) (t 1) (t 2) 0 1 0 (ht 0) hj (ht 2)
  | 2, hj => rectangleCoeff K (t 0) (t 1) (t 2) 0 0 1 (ht 0) (ht 1) hj

theorem selectedFirst_mul (t : Fin 3 → ℕ) (ht : ∀ j, 0 < t j)
    (j : Fin 3) (hj : 1<t j) (x y : RectangleJet K (t 0) (t 1) (t 2)) :
    selectedFirst K t ht j hj (x*y) =
      rectangleResidue K (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2) x *
        selectedFirst K t ht j hj y +
      rectangleResidue K (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2) y *
        selectedFirst K t ht j hj x := by
  have hs : Function.Surjective (rectangleProjection K (t 0) (t 1) (t 2)) := by
    apply Function.Surjective.comp
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (jetProjection (Jet (Jet K (t 2)) (t 1)) (t 0)))
    apply Function.Surjective.comp
      (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)
    exact PowerSeries.map_surjective _
      (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)
  obtain ⟨f, rfl⟩ := hs x
  obtain ⟨g, rfl⟩ := hs y
  rw [← map_mul]
  fin_cases j <;>
    simp only [selectedFirst, rectangleCoeff_projection, rectangleResidue_projection] <;>
    simp only [PowerSeries.coeff_one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_add, map_mul] <;> ring

variable [Algebra ℚ K]

def selectedAugmentationFirst (t : Fin 3 → ℕ) (ht : ∀ j, 0 < t j)
    (j : Fin 3) (hj : 1<t j) :
    rectangleAugmentation K (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2) →ₗ[ℚ] K :=
  (selectedFirst K t ht j hj).toRatLinearMap.comp
    ((rectangleAugmentation K (t 0) (t 1) (t 2)
      (ht 0) (ht 1) (ht 2)).restrictScalars ℚ).subtype

theorem selectedAugmentationFirst_product_zero (t : Fin 3 → ℕ) (ht : ∀ j, 0<t j)
    (j : Fin 3) (hj : 1<t j)
    (x y : rectangleAugmentation K (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2)) :
    selectedAugmentationFirst K t ht j hj (x*y) = 0 := by
  change selectedFirst K t ht j hj ((x : RectangleJet K (t 0) (t 1) (t 2))*y) = 0
  rw [selectedFirst_mul]
  have hx := x.property
  have hy := y.property
  change rectangleResidue K (t 0) (t 1) (t 2) _ _ _ x = 0 at hx
  change rectangleResidue K (t 0) (t 1) (t 2) _ _ _ y = 0 at hy
  rw [hx, hy, zero_mul, zero_mul, add_zero]

def selectedCotangentCoefficient (t : Fin 3 → ℕ) (ht : ∀ j, 0<t j)
    (j : Fin 3) (hj : 1<t j) :
    (rectangleAugmentation K (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2)).Cotangent →ₗ[ℚ] K :=
  Ideal.Cotangent.lift (selectedAugmentationFirst K t ht j hj)
    (selectedAugmentationFirst_product_zero K t ht j hj)

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem selectedFirst_taylor (D : Fin 3 → Derivation ℚ R R) (ρ : R →+* K)
    (t : Fin 3 → ℕ) (ht : ∀ j, 0<t j) (j : Fin 3) (hj : 1<t j) (f : R) :
    selectedFirst K t ht j hj
      (rectangularJetHom K (D 0) (D 1) (D 2) ρ (t 0) (t 1) (t 2) f) = ρ (D j f) := by
  fin_cases j <;> simp [selectedFirst, rectangleCoeff_taylor]

def selectedSourceTaylorCotangent (I : Ideal R) (D : Fin 3 → Derivation ℚ R R)
    (t : Fin 3 → ℕ) (ht : ∀ j, 0<t j) :
    I.Cotangent →ₗ[ℚ]
      (rectangleAugmentation (R ⧸ I) (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2)).Cotangent :=
  Ideal.mapCotangent I
    (rectangleAugmentation (R ⧸ I) (t 0) (t 1) (t 2) (ht 0) (ht 1) (ht 2))
    (rectangularJetAlgHom (R ⧸ I) D (Ideal.Quotient.mk I) (t 0) (t 1) (t 2))
    (by
      change I ≤ (rectangleAugmentation (R ⧸ I) (t 0) (t 1) (t 2) _ _ _).comap
        (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) (t 0) (t 1) (t 2))
      rw [quotientTaylor_augmentation_comap])

theorem selectedSourceTaylorCotangent_coefficient (I : Ideal R)
    (D : Fin 3 → Derivation ℚ R R) (t : Fin 3 → ℕ) (ht : ∀ j, 0<t j)
    (j : Fin 3) (hj : 1<t j) (z : I.Cotangent) :
    selectedCotangentCoefficient (R ⧸ I) t ht j hj
      (selectedSourceTaylorCotangent I D t ht z) =
      SiegelZeros.W58.derivationNormal I (D j) z := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  change selectedFirst (R ⧸ I) t ht j hj
    (rectangularJetHom (R ⧸ I) (D 0) (D 1) (D 2) (Ideal.Quotient.mk I) (t 0) (t 1) (t 2) x) =
      Ideal.Quotient.mk I (D j x)
  exact selectedFirst_taylor (R ⧸ I) D (Ideal.Quotient.mk I) t ht j hj x

end Result.Workers.W57

end SiegelZeros

end

end OAI
