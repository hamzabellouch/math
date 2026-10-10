import Mathlib

namespace OAI

/-! Tensor domains over algebraically or relatively closed fields. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators

 

theorem finiteType_nonzero_specialization
    (K S : Type*) [Field K] [IsAlgClosed K] [CommRing S] [IsDomain S]
    [Algebra K S] [Algebra.FiniteType K S] (a : S) (ha : a ≠ 0) :
    ∃ φ : S →ₐ[K] K, φ a ≠ 0 := by
  let T := Localization.Away a
  have hinj : Function.Injective (algebraMap S T) :=
    IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  let : Nontrivial T := hinj.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := T)
  let : m.IsMaximal := hm
  let : Field (T ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ m)
  let j : (T ⧸ m) →ₐ[K] K := IsAlgClosed.lift
  let φ : S →ₐ[K] K := j.comp
    ((Ideal.Quotient.mkₐ K m).comp (IsScalarTower.toAlgHom K S T))
  refine ⟨φ, ?_⟩
  exact (IsUnit.map (j.comp
    (Ideal.Quotient.mkₐ K m)) (IsLocalization.Away.algebraMap_isUnit a (S := T))).ne_zero

def tensorSubalgebraInclusion (K M S : Type*) [Field K] [CommRing M] [CommRing S]
    [Algebra K M] [Algebra K S] (A : Subalgebra K S) : M ⊗[K] A →ₐ[K] M ⊗[K] S :=
  Algebra.TensorProduct.map (AlgHom.id K M) A.val

lemma tensorSubalgebraInclusion_transition
    (K M S : Type*) [Field K] [CommRing M] [CommRing S]
    [Algebra K M] [Algebra K S] {A B : Subalgebra K S} (h : A ≤ B) (x : M ⊗[K] A) :
    tensorSubalgebraInclusion K M S B
      (Algebra.TensorProduct.map (AlgHom.id K M) (Subalgebra.inclusion h) x) =
      tensorSubalgebraInclusion K M S A x := by
  induction x using TensorProduct.inductionOn with
  | tmul m a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensor_finiteType_field_of_definition
    (K M S : Type*) [Field K] [CommRing M] [CommRing S]
    [Algebra K M] [Algebra K S] (x : M ⊗[K] S) :
    ∃ (A : Subalgebra K S), A.FG ∧ ∃ y : M ⊗[K] A,
      tensorSubalgebraInclusion K M S A y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul m s =>
      exact ⟨Algebra.adjoin K {s}, ⟨{s}, by simp⟩,
        m ⊗ₜ[K] (⟨s, Algebra.subset_adjoin (Set.mem_singleton s)⟩ : Algebra.adjoin K {s}), rfl⟩
  | add x y hx hy =>
      obtain ⟨A, hA, x', hx'⟩ := hx
      obtain ⟨B, hB, y', hy'⟩ := hy
      refine ⟨A ⊔ B, hA.sup hB,
        Algebra.TensorProduct.map (AlgHom.id K M) (Subalgebra.inclusion le_sup_left) x' +
        Algebra.TensorProduct.map (AlgHom.id K M) (Subalgebra.inclusion le_sup_right) y', ?_⟩
      rw [map_add, tensorSubalgebraInclusion_transition,
        tensorSubalgebraInclusion_transition, hx', hy']

lemma tensor_specialization_coordinate
    (K M S : Type*) [Field K] [CommRing M] [CommRing S]
    [Algebra K M] [Algebra K S] {ι : Type*} [DecidableEq ι] (b : Module.Basis ι K M)
    (φ : S →ₐ[K] K) (z : M ⊗[K] S) (i : ι) :
    b.repr (AlgHom.liftEquiv K M S M ((Algebra.ofId K M).comp φ) z) i =
      φ ((TensorProduct.equivFinsuppOfBasisLeft b) z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul m s =>
      simp [mul_comm]
      rw [mul_comm m _, ← Algebra.smul_def, map_smul]
      rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

 

theorem tensor_domain_of_algClosed_finiteType
    (K M S : Type*) [Field K] [IsAlgClosed K] [CommRing M] [IsDomain M]
    [CommRing S] [IsDomain S] [Algebra K M] [Algebra K S] [Algebra.FiniteType K S] :
    IsDomain (M ⊗[K] S) := by
  classical
  let b := Module.Free.chooseBasis K M
  have hnz : ∀ z : M ⊗[K] S, z ≠ 0 →
      ∃ i, TensorProduct.equivFinsuppOfBasisLeft b z i ≠ 0 := by
    intro z hz
    by_contra! h
    apply hz
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    simpa using h i
  have hnd : NoZeroDivisors (M ⊗[K] S) := ⟨by
    intro x y hxy
    by_contra! h
    obtain ⟨i, hi⟩ := hnz x h.1
    obtain ⟨j, hj⟩ := hnz y h.2
    obtain ⟨φ, hφ⟩ := finiteType_nonzero_specialization K S
      ((TensorProduct.equivFinsuppOfBasisLeft b x i) *
        (TensorProduct.equivFinsuppOfBasisLeft b y j)) (mul_ne_zero hi hj)
    let e := AlgHom.liftEquiv K M S M ((Algebra.ofId K M).comp φ)
    have hex : e x ≠ 0 := by
      intro hx
      have hv := tensor_specialization_coordinate K M S b φ x i
      rw [show e x = 0 from hx] at hv
      apply hφ
      rw [map_mul, ← hv]
      simp
    have hey : e y ≠ 0 := by
      intro hy
      have hv := tensor_specialization_coordinate K M S b φ y j
      rw [show e y = 0 from hy] at hv
      apply hφ
      rw [map_mul, ← hv]
      simp
    apply mul_ne_zero hex hey
    rw [← map_mul, hxy, map_zero]⟩
  let := hnd
  let : Nontrivial (M ⊗[K] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left K M S
      (Algebra.linearMap K S) (FaithfulSMul.algebraMap_injective K S)
  exact NoZeroDivisors.to_isDomain _

 

theorem tensor_domain_of_algClosed
    (K M S : Type*) [Field K] [IsAlgClosed K] [CommRing M] [IsDomain M]
    [CommRing S] [IsDomain S] [Algebra K M] [Algebra K S] :
    IsDomain (M ⊗[K] S) := by
  classical
  have hnd : NoZeroDivisors (M ⊗[K] S) := ⟨by
    intro x y hxy
    obtain ⟨A, hA, x', hx'⟩ := tensor_finiteType_field_of_definition K M S x
    obtain ⟨B, hB, y', hy'⟩ := tensor_finiteType_field_of_definition K M S y
    let C := A ⊔ B
    let : Algebra.FiniteType K C := (Subalgebra.fg_iff_finiteType C).mp (hA.sup hB)
    let : IsDomain (M ⊗[K] C) := tensor_domain_of_algClosed_finiteType K M C
    let xc : M ⊗[K] C := Algebra.TensorProduct.map (AlgHom.id K M)
      (Subalgebra.inclusion (show A ≤ C from le_sup_left)) x'
    let yc : M ⊗[K] C := Algebra.TensorProduct.map (AlgHom.id K M)
      (Subalgebra.inclusion (show B ≤ C from le_sup_right)) y'
    let t := tensorSubalgebraInclusion K M S C
    have hxc : t xc = x := (tensorSubalgebraInclusion_transition K M S le_sup_left x').trans hx'
    have hyc : t yc = y := (tensorSubalgebraInclusion_transition K M S le_sup_right y').trans hy'
    have ht : Function.Injective t := by
      change Function.Injective (LinearMap.lTensor M C.val.toLinearMap)
      exact Module.Flat.lTensor_preserves_injective_linearMap C.val.toLinearMap Subtype.val_injective
    have hzero : xc * yc = 0 := ht (by simpa only [map_mul, hxc, hyc, map_zero] using hxy)
    rcases mul_eq_zero.mp hzero with hx | hy
    · exact Or.inl (hxc.symm.trans (by rw [hx, map_zero]))
    · exact Or.inr (hyc.symm.trans (by rw [hy, map_zero]))⟩
  let := hnd
  let : Nontrivial (M ⊗[K] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left K M S
      (Algebra.linearMap K S) (FaithfulSMul.algebraMap_injective K S)
  exact NoZeroDivisors.to_isDomain _

end RelativeDenominators

open Polynomial
open scoped TensorProduct
namespace RelativeDenominators

 

theorem minpoly_map_of_relatively_closed
    (K M E : Type*) [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
    [IsIntegrallyClosedIn K M] (x : E) (hx : IsIntegral K x) :
    (minpoly K x).map (algebraMap K M) = minpoly M x := by
  apply minpoly.map_algebraMap hx
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro i
  apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
  exact Polynomial.isIntegral_coeff_of_dvd (minpoly K x) (minpoly M x)
    (minpoly.monic hx) (minpoly.monic hx.tower_top)
    (minpoly.dvd_map_of_isScalarTower K M x) i

 

theorem tensor_domain_of_relatively_closed_finite_separable
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [IsIntegrallyClosedIn K M]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : IsDomain (M ⊗[K] L) := by
  let E := AlgebraicClosure M
  let j : L →ₐ[K] E := IsAlgClosed.lift
  let b := Field.powerBasisOfFiniteOfSeparable K L
  let t : M ⊗[K] L →ₐ[M] E := AlgHom.liftEquiv K M L E j
  have hint : IsIntegral K (j b.gen) := b.isIntegral_gen.map j
  have hmin : minpoly M (j b.gen) = (minpoly K b.gen).map (algebraMap K M) := by
    rw [← minpoly_map_of_relatively_closed K M E (j b.gen) hint,
      minpoly.algHom_eq j j.injective]
  have hdeg : (minpoly M (j b.gen)).natDegree = b.dim := by
    rw [hmin, Polynomial.natDegree_map, b.natDegree_minpoly]
  have hlin : LinearIndependent M (t.toLinearMap ∘ b.basis.baseChange M) := by
    have hi := linearIndependent_pow (K := M) (j b.gen)
    rw [hdeg] at hi
    convert hi using 1
    ext i
    simp [t, b.basis_eq_pow]
  exact (LinearMap.injective_of_linearIndependent
    (b.basis.baseChange M).span_eq hlin).isDomain t.toRingHom

 

theorem tensor_domain_of_finiteType_subalgebras
    (K M S : Type*) [Field K] [CommRing M] [IsDomain M]
    [CommRing S] [IsDomain S] [Algebra K M] [Algebra K S]
    (h : ∀ A : Subalgebra K S, A.FG → IsDomain (M ⊗[K] A)) :
    IsDomain (M ⊗[K] S) := by
  classical
  have hnd : NoZeroDivisors (M ⊗[K] S) := ⟨by
    intro x y hxy
    obtain ⟨A, hA, x', hx'⟩ := tensor_finiteType_field_of_definition K M S x
    obtain ⟨B, hB, y', hy'⟩ := tensor_finiteType_field_of_definition K M S y
    let C := A ⊔ B
    let : IsDomain (M ⊗[K] C) := h C (hA.sup hB)
    let xc : M ⊗[K] C := Algebra.TensorProduct.map (AlgHom.id K M)
      (Subalgebra.inclusion (show A ≤ C from le_sup_left)) x'
    let yc : M ⊗[K] C := Algebra.TensorProduct.map (AlgHom.id K M)
      (Subalgebra.inclusion (show B ≤ C from le_sup_right)) y'
    let t := tensorSubalgebraInclusion K M S C
    have hxc : t xc = x := (tensorSubalgebraInclusion_transition K M S le_sup_left x').trans hx'
    have hyc : t yc = y := (tensorSubalgebraInclusion_transition K M S le_sup_right y').trans hy'
    have ht : Function.Injective t := by
      change Function.Injective (LinearMap.lTensor M C.val.toLinearMap)
      exact Module.Flat.lTensor_preserves_injective_linearMap C.val.toLinearMap Subtype.val_injective
    have hzero : xc * yc = 0 := ht (by simpa only [map_mul, hxc, hyc, map_zero] using hxy)
    rcases mul_eq_zero.mp hzero with hx | hy
    · exact Or.inl (hxc.symm.trans (by rw [hx, map_zero]))
    · exact Or.inr (hyc.symm.trans (by rw [hy, map_zero]))⟩
  let := hnd
  let : Nontrivial (M ⊗[K] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left K M S
      (Algebra.linearMap K S) (FaithfulSMul.algebraMap_injective K S)
  exact NoZeroDivisors.to_isDomain _

 

theorem tensor_domain_of_relatively_closed_algebraic
    (K M L : Type*) [Field K] [CharZero K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [IsIntegrallyClosedIn K M]
    [Algebra.IsAlgebraic K L] : IsDomain (M ⊗[K] L) := by
  apply tensor_domain_of_finiteType_subalgebras K M L
  intro A hA
  let : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  let : Algebra.IsAlgebraic K A := Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  let : Field A := (isField_of_isIntegral_of_isField' (Field.toIsField K)).toField
  let : Module.Finite K A := Algebra.IsIntegral.finite
  exact tensor_domain_of_relatively_closed_finite_separable K M A

 

theorem tensor_domain_of_relatively_closed
    (K M L : Type*) [Field K] [CharZero K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [IsIntegrallyClosedIn K M] : IsDomain (M ⊗[K] L) := by
  let C := AlgebraicClosure K
  let E := AlgebraicClosure L
  let j : C →ₐ[K] E := IsAlgClosed.lift
  let : Algebra C E := j.toRingHom.toAlgebra
  let : IsScalarTower K C E := IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
  let : IsDomain (M ⊗[K] C) := tensor_domain_of_relatively_closed_algebraic K M C
  let : IsDomain (C ⊗[K] M) :=
    (Algebra.TensorProduct.comm K C M).injective.isDomain
      (Algebra.TensorProduct.comm K C M).toRingHom
  let : IsDomain (E ⊗[C] (C ⊗[K] M)) := tensor_domain_of_algClosed C E (C ⊗[K] M)
  let e := Algebra.TensorProduct.cancelBaseChange K C E E M
  let : IsDomain (E ⊗[K] M) := e.symm.injective.isDomain e.symm.toRingHom
  let t : L ⊗[K] M →ₐ[K] E ⊗[K] M :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L E) (AlgHom.id K M)
  have ht : Function.Injective t := by
    change Function.Injective (LinearMap.rTensor M (IsScalarTower.toAlgHom K L E).toLinearMap)
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective (algebraMap L E))
  let : IsDomain (L ⊗[K] M) := ht.isDomain t.toRingHom
  exact (Algebra.TensorProduct.comm K M L).injective.isDomain
    (Algebra.TensorProduct.comm K M L).toRingHom

end RelativeDenominators

end

end OAI
