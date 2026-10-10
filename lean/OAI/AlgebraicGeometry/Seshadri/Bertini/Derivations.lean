import Mathlib

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem aeval_injective_of_derivation {R A : Type*}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [IsDomain A] [Algebra R A]
    (hRA : Function.Injective (algebraMap R A))
    (D : Derivation R A A) (x : A) (hx : D x ≠ 0) :
    Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  apply (injective_iff_map_eq_zero (Polynomial.aeval x : R[X] →ₐ[R] A)).mpr
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hp
    by_cases h0 : p.natDegree = 0
    · have he := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [he, Polynomial.aeval_C] at hp
      have hc : p.coeff 0 = 0 := hRA (hp.trans (map_zero (algebraMap R A)).symm)
      rw [he, hc, Polynomial.C_0]
    · have hd : Polynomial.aeval x p.derivative = 0 := by
        have hd := congrArg D hp
        rw [D.map_zero, D.map_aeval] at hd
        change Polynomial.aeval x p.derivative * D x = 0 at hd
        exact (mul_eq_zero.mp hd).resolve_right hx
      have hdz : p.derivative = 0 := ih p.derivative.natDegree
        (hn ▸ Polynomial.natDegree_derivative_lt h0) p.derivative rfl hd
      exact (h0 (Polynomial.derivative_eq_zero.mp hdz)).elim

def mvCoeffDerivation {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) : Derivation K (MvPolynomial σ A) (MvPolynomial σ A) where
  toFun := AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom
  map_add' p q := by ext m; simp
  map_smul' k p := by ext m; simp
  map_one_eq_zero' := by
    ext m
    simp [MvPolynomial.coeff_one, apply_ite D]
  leibniz' p q := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [add_mul, map_add, add_smul, smul_add, hp, hq]
      abel
    | monomial m a =>
      induction q using MvPolynomial.induction_on' with
      | add p q hp hq =>
        simp only [mul_add, map_add, add_smul, smul_add, hp, hq]
        abel
      | monomial n b =>
        have hm (u : σ →₀ ℕ) (c : A) :
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial u c) =
              MvPolynomial.monomial u (D c) := by
          ext t
          simp [MvPolynomial.coeff_monomial, apply_ite D]
        change AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom
            (MvPolynomial.monomial m a * MvPolynomial.monomial n b) =
          MvPolynomial.monomial m a *
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial n b) +
          MvPolynomial.monomial n b *
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial m a)
        rw [MvPolynomial.monomial_mul_monomial, hm, hm, hm, D.leibniz]
        simp only [smul_eq_mul, map_add, MvPolynomial.monomial_mul_monomial, add_comm n m]

@[simp] theorem mvCoeffDerivation_coeff {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (p : MvPolynomial σ A) (m) :
    (mvCoeffDerivation D p).coeff m = D (p.coeff m) := rfl

@[simp] theorem mvCoeffDerivation_C {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (a : A) :
    mvCoeffDerivation (σ := σ) D (MvPolynomial.C a) = MvPolynomial.C (D a) := by
  ext m
  simp [MvPolynomial.coeff_C, apply_ite D]

@[simp] theorem mvCoeffDerivation_X {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (i : σ) :
    mvCoeffDerivation D (MvPolynomial.X i) = 0 := by
  ext m
  simp [MvPolynomial.coeff_X, apply_ite D]

@[simp] theorem mvCoeffDerivation_algebraMap {K A σ : Type*}
    [CommRing K] [CommRing A] [Algebra K A] (D : Derivation K A A)
    (p : MvPolynomial σ K) :
    mvCoeffDerivation D (algebraMap (MvPolynomial σ K) (MvPolynomial σ A) p) = 0 := by
  ext m
  simp [MvPolynomial.coeff_map]

def mvParameterDerivation {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) :
    Derivation (MvPolynomial σ K) (MvPolynomial σ A) (MvPolynomial σ A) where
  toFun := mvCoeffDerivation D
  map_add' := map_add (mvCoeffDerivation D)
  map_smul' r p := by
    rw [Algebra.smul_def, (mvCoeffDerivation D).leibniz,
      mvCoeffDerivation_algebraMap, smul_zero, add_zero, Algebra.smul_def]
    rfl
  map_one_eq_zero' := (mvCoeffDerivation D).map_one_eq_zero
  leibniz' := (mvCoeffDerivation D).leibniz

theorem hyperplane_aeval_injective {K A σ : Type*} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    (v : σ → A) (D : Derivation K A A) (i : σ) (hi : D (v i) ≠ 0) :
    Function.Injective (Polynomial.aeval (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ K) (MvPolynomial σ A)) := by
    exact MvPolynomial.map_injective (algebraMap K A) (algebraMap K A).injective
  apply aeval_injective_of_derivation hinj (mvParameterDerivation D)
  have he : mvParameterDerivation D (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) =
      ∑ j, MvPolynomial.C (D (v j)) * MvPolynomial.X j := by
    change (mvCoeffDerivation (σ := σ) D)
      (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [(mvCoeffDerivation D).leibniz, mvCoeffDerivation_C, mvCoeffDerivation_X]
    change MvPolynomial.C (v j) * 0 + MvPolynomial.X j * MvPolynomial.C (D (v j)) =
      MvPolynomial.C (D (v j)) * MvPolynomial.X j
    rw [mul_zero, zero_add, mul_comm]
  rw [he]
  intro hz
  have hh := congrArg (MvPolynomial.eval (fun j => if j = i then (1 : A) else 0)) hz
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    map_zero] at hh
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hh
  exact hi hh

end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem genericFiber_isDomain {P B : Type*} [CommRing P] [IsDomain P]
    [CommRing B] [IsDomain B] [Algebra P B]
    (h : Function.Injective (algebraMap P B)) :
    IsDomain (FractionRing P ⊗[P] B) := by
  let : Algebra B (FractionRing P ⊗[P] B) := Algebra.TensorProduct.rightAlgebra
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M :=
    Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
  rintro z ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hz
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (h (by simpa using hz))

def doubledBaseChangeEquiv {P F B : Type*} [CommRing P] [CommRing F]
    [CommRing B] [Algebra P F] [Algebra P B] :
    ((F ⊗[P] B) ⊗[F] (F ⊗[P] B)) ≃ₐ[F] F ⊗[P] (B ⊗[P] B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm P P F F F B F B).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid F F) (AlgEquiv.refl :
      (B ⊗[P] B) ≃ₐ[P] B ⊗[P] B))

theorem doubledGenericFiber_isDomain {P B : Type*} [CommRing P] [IsDomain P]
    [CommRing B] [IsDomain B] [Algebra P B]
    (h : Function.Injective (algebraMap P B)) [IsDomain (B ⊗[P] B)] :
    IsDomain ((FractionRing P ⊗[P] B) ⊗[FractionRing P] (FractionRing P ⊗[P] B)) := by
  have hP : Function.Injective (algebraMap P (B ⊗[P] B)) := by
    intro x y hxy
    apply h
    simpa only [AlgHom.commutes] using congrArg (Algebra.TensorProduct.lmul' P (S := B)) hxy
  let : IsDomain (FractionRing P ⊗[P] (B ⊗[P] B)) := genericFiber_isDomain hP
  let e := doubledBaseChangeEquiv (P := P) (F := FractionRing P) (B := B)
  exact e.injective.isDomain e.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem finiteType_rationalPoint {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [Nontrivial A] [Algebra K A] [Algebra.FiniteType K A] :
    Nonempty (A →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

theorem finiteType_point_nonvanishing {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (a : A) (ha : a ≠ 0) : ∃ f : A →ₐ[K] K, f a ≠ 0 := by
  let C := Localization.Away a
  have hs : Submonoid.powers a ≤ nonZeroDivisors A := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n ha)
  let : IsDomain C := IsLocalization.isDomain_localization hs
  obtain ⟨φ⟩ := finiteType_rationalPoint (K := K) (A := C)
  let j : A →ₐ[K] C := IsScalarTower.toAlgHom K A C
  refine ⟨φ.comp j, ?_⟩
  exact ((IsLocalization.map_units C (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)).map
    φ.toMonoidHom).ne_zero

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri
noncomputable section
open scoped TensorProduct

variable {F A B : Type} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

def tensorSpecialize (φ : A →ₐ[F] F) : A ⊗[F] B →ₐ[F] B :=
  (Algebra.TensorProduct.lid F B).toAlgHom.comp
    (Algebra.TensorProduct.map φ (AlgHom.id F B))

lemma tensorSpecialize_repr {ι : Type} (b : Module.Basis ι F B)
    (φ : A →ₐ[F] F) (z : A ⊗[F] B) (i : ι) :
    b.repr (tensorSpecialize φ z) i = φ ((b.baseChange A).repr z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [tensorSpecialize, Module.Basis.baseChange_repr_tmul, map_smul, mul_comm]
  | add x y hx hy => simp_all

theorem tensorProduct_isDomain [IsAlgClosed F] 
    [IsDomain A] [IsDomain B] [Algebra.FiniteType F A] : IsDomain (A ⊗[F] B) := by
  classical
  let b := Module.Basis.ofVectorSpace F B
  have hex (z : A ⊗[F] B) (hz : z ≠ 0) :
      ∃ i, (b.baseChange A).repr z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    apply (b.baseChange A).repr.injective
    ext i
    simpa using h i
  let : Nontrivial (A ⊗[F] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F A B
      (algebraMap F A).injective (algebraMap F B).injective
  let : NoZeroDivisors (A ⊗[F] B) := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hex x h.1
    obtain ⟨j, hj⟩ := hex y h.2
    obtain ⟨ψ, hψ⟩ := BertiniIntegral.finiteType_point_nonvanishing (K := F)
      ((b.baseChange A).repr x i * (b.baseChange A).repr y j) (mul_ne_zero hi hj)
    rw [map_mul, mul_ne_zero_iff] at hψ
    have hx : tensorSpecialize (B := B) ψ x ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ x i
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.1 this.symm
    have hy : tensorSpecialize (B := B) ψ y ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ y j
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.2 this.symm
    have := congrArg (tensorSpecialize (B := B) ψ) hxy
    simp only [map_mul, map_zero, mul_eq_zero, hx, hy, or_self] at this⟩
  exact NoZeroDivisors.to_isDomain _

end
end MaximalSeshadri


end
end

end OAI
