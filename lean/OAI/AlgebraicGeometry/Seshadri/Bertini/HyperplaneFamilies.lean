import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.GenericHyperplanes
import OAI.AlgebraicGeometry.Seshadri.Bertini.GeometricDomains

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

@[instance_reducible] def hyperplaneFamilyAlgebra {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Fintype σ] (v : σ → A) :
    Algebra (MvPolynomial σ K)[X] (MvPolynomial σ A) :=
  (Polynomial.aeval (homogeneousLinearForm v) :
    (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A).toRingHom.toAlgebra

instance hyperplaneFamilyAlgebra_tower {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Fintype σ] (v : σ → A) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsScalarTower (MvPolynomial σ K) (MvPolynomial σ K)[X] (MvPolynomial σ A) := by
  let := hyperplaneFamilyAlgebra (K := K) v
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change algebraMap (MvPolynomial σ K) (MvPolynomial σ A) p =
    Polynomial.aeval (homogeneousLinearForm v) (Polynomial.C p)
  rw [Polynomial.aeval_C]

theorem hyperplaneFamily_geometricGeneric {K A E σ : Type} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    [IsDomain (A ⊗[K] A)] [Field E]
    [Algebra (FractionRing (MvPolynomial σ K)[X]) E]
    (v : σ → A) (D : Derivation K A A) (k : σ) (hk : D (v k) ≠ 0)
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]] E) := by
  let := hyperplaneFamilyAlgebra (K := K) v
  let := hyperplaneFamilyAlgebra_tower (K := K) v
  have hdom : Function.Injective (algebraMap (MvPolynomial σ K)[X] (MvPolynomial σ A)) :=
    hyperplane_aeval_injective v D k hk
  let : IsDomain (MvPolynomial σ A ⊗[(MvPolynomial σ K)[X]] MvPolynomial σ A) :=
    hyperplaneFamily_double_isDomain v (by change Polynomial.aeval _ X = _; simp) i j hji hi hij
  let : IsDomain (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) := genericFiber_isDomain hdom
  let : IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]]
      (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A)) := doubledGenericFiber_isDomain hdom
  exact self_tensor_domain_geometrically_domain_algebra

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_parameter_tensor {R K A σ : Type*}
    [CommRing R] [CommRing K] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra (MvPolynomial σ R) K] [IsScalarTower R (MvPolynomial σ R) K] :
    ∃ e : (K ⊗[MvPolynomial σ R] MvPolynomial σ A) ≃ₐ[K] (K ⊗[R] A),
      (∀ k a, e (k ⊗ₜ[MvPolynomial σ R] C a) = k ⊗ₜ[R] a) ∧
      ∀ i, e (1 ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A)) =
        (algebraMap (MvPolynomial σ R) K (X i)) ⊗ₜ[R] 1 := by
  let D := K ⊗[R] A
  let Q := K ⊗[MvPolynomial σ R] MvPolynomial σ A
  let α : σ → K := fun i => algebraMap (MvPolynomial σ R) K (X i)
  let ev : MvPolynomial σ A →ₐ[R] D :=
    { MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : A →ₐ[R] D).toRingHom
        (fun i => α i ⊗ₜ[R] (1 : A)) with
      commutes' := fun r => by
        simp only [MvPolynomial.algebraMap_apply]
        change MvPolynomial.eval₂
          (Algebra.TensorProduct.includeRight : A →ₐ[R] D).toRingHom
          (fun i => α i ⊗ₜ[R] (1 : A)) (C (algebraMap R A r)) = _
        rw [MvPolynomial.eval₂_C]
        exact (Algebra.TensorProduct.includeRight : A →ₐ[R] D).commutes r }
  have heC (a : A) : ev (C a) = (1 : K) ⊗ₜ[R] a := by
    simp only [ev, AlgHom.coe_mk, coe_eval₂Hom, eval₂_C]
    rfl
  have heX (i : σ) : ev (X i) = α i ⊗ₜ[R] (1 : A) := by simp [ev]
  have hemap : ev.toRingHom.comp (algebraMap (MvPolynomial σ R) (MvPolynomial σ A)) =
      algebraMap (MvPolynomial σ R) D := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
      change ev (C (algebraMap R A r)) = algebraMap (MvPolynomial σ R) D (C r)
      rw [heC]
      change (1 : K) ⊗ₜ[R] algebraMap R A r =
        algebraMap (MvPolynomial σ R) D (algebraMap R (MvPolynomial σ R) r)
      rw [← IsScalarTower.algebraMap_apply]
      change (1 : K) ⊗ₜ[R] algebraMap R A r = (algebraMap R K r) ⊗ₜ[R] (1 : A)
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      change ev (X i) = algebraMap (MvPolynomial σ R) D (X i)
      rw [heX]
      rfl
  let evP : MvPolynomial σ A →ₐ[MvPolynomial σ R] D :=
    ⟨ev.toRingHom, fun p => DFunLike.congr_fun hemap p⟩
  let f : Q →ₐ[MvPolynomial σ R] D := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom (MvPolynomial σ R) K D) evP (fun _ _ => Commute.all _ _)
  let lc : K →ₐ[R] Q :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[MvPolynomial σ R] Q).restrictScalars R
  let rc : A →ₐ[R] Q :=
    ((Algebra.TensorProduct.includeRight : MvPolynomial σ A →ₐ[MvPolynomial σ R] Q).restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (MvPolynomial σ A))
  let g : D →ₐ[R] Q := Algebra.TensorProduct.lift lc rc (fun _ _ => Commute.all _ _)
  have hgt (k : K) (a : A) : g (k ⊗ₜ[R] a) = k ⊗ₜ[MvPolynomial σ R] C a := by
    change (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) *
      ((1 : K) ⊗ₜ[MvPolynomial σ R] C a) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hft (k : K) (p : MvPolynomial σ A) :
      f (k ⊗ₜ[MvPolynomial σ R] p) = (k ⊗ₜ[R] (1 : A)) * ev p := rfl
  have hfC (k : K) (a : A) : f (k ⊗ₜ[MvPolynomial σ R] C a) = k ⊗ₜ[R] a := by
    rw [hft, heC]
    change (k ⊗ₜ[R] (1 : A)) * ((1 : K) ⊗ₜ[R] a) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hfX (i : σ) : f (1 ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A)) =
      α i ⊗ₜ[R] (1 : A) := by
    rw [hft, heX]
    change ((1 : K) ⊗ₜ[R] (1 : A)) * (α i ⊗ₜ[R] (1 : A)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  have hgX (i : σ) : g (ev (X i)) = (1 : K) ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A) := by
    rw [heX, hgt, map_one]
    have h := TensorProduct.smul_tmul (R := MvPolynomial σ R)
      (X i : MvPolynomial σ R) (1 : K) (1 : MvPolynomial σ A)
    simpa only [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_def, MvPolynomial.map_X] using h
  have hgC (p : MvPolynomial σ A) : g (ev p) = (1 : K) ⊗ₜ[MvPolynomial σ R] p := by
    induction p using MvPolynomial.induction_on with
    | C a => rw [heC, hgt]
    | add p q hp hq => simp only [map_add, hp, hq, TensorProduct.tmul_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, hgX]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hgf : ∀ x : Q, g (f x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k p =>
      rw [hft, map_mul, hgt, hgC, map_one]
      change (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) *
        ((1 : K) ⊗ₜ[MvPolynomial σ R] p) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hfg : ∀ x : D, f (g x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k a => rw [hgt, hfC]
  let fK : Q →ₐ[K] D :=
    { f.toRingHom with
      commutes' := by
        intro k
        change f (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) = k ⊗ₜ[R] (1 : A)
        simpa only [map_one] using hfC k 1 }
  let e := AlgEquiv.ofBijective fK ⟨Function.LeftInverse.injective hgf,
    Function.RightInverse.surjective hfg⟩
  exact ⟨e, hfC, hfX⟩

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

theorem tensor_base_polynomial_relation {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra R[X] A] [Algebra R[X] B]
    [IsScalarTower R R[X] A] [IsScalarTower R R[X] B] :
    ∃ e : ((A ⊗[R] B) ⧸ Ideal.span
      {algebraMap R[X] A X ⊗ₜ[R] (1 : B) - (1 : A) ⊗ₜ[R] algebraMap R[X] B X})
        ≃ₐ[A] (A ⊗[R[X]] B),
      ∀ (x : A) (y : B), e (Ideal.Quotient.mk _ (x ⊗ₜ[R] y)) = x ⊗ₜ[R[X]] y := by
  let a := algebraMap R[X] A X
  let b := algebraMap R[X] B X
  let T := A ⊗[R] B
  let D := A ⊗[R[X]] B
  let I : Ideal T := Ideal.span {a ⊗ₜ[R] (1 : B) - (1 : A) ⊗ₜ[R] b}
  let Q := T ⧸ I
  let q : T →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let l : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeLeft
  let r : B →ₐ[R] Q := q.comp Algebra.TensorProduct.includeRight
  have he : l a = r b := by
    apply sub_eq_zero.mp
    change q (a ⊗ₜ[R] 1) - q (1 ⊗ₜ[R] b) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hp : l.toRingHom.comp (algebraMap R[X] A) =
      r.toRingHom.comp (algebraMap R[X] B) := by
    apply Polynomial.ringHom_ext
    · intro z
      change l (algebraMap R[X] A (C z)) = r (algebraMap R[X] B (C z))
      change l (algebraMap R[X] A (algebraMap R R[X] z)) =
        r (algebraMap R[X] B (algebraMap R R[X] z))
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      rw [l.commutes, r.commutes]
    · exact he
  let lp : A →ₐ[R[X]] Q := ⟨l.toRingHom, fun _ => rfl⟩
  let rp : B →ₐ[R[X]] Q := ⟨r.toRingHom, fun z => (DFunLike.congr_fun hp z).symm⟩
  let g : D →ₐ[R] Q := (Algebra.TensorProduct.lift lp rp
    (fun _ _ => Commute.all _ _)).restrictScalars R
  let dl : A →ₐ[R] D := (Algebra.TensorProduct.includeLeft : A →ₐ[R[X]] D).restrictScalars R
  let dr : B →ₐ[R] D := (Algebra.TensorProduct.includeRight : B →ₐ[R[X]] D).restrictScalars R
  let f : T →ₐ[R] D := Algebra.TensorProduct.lift dl dr (fun _ _ => Commute.all _ _)
  have hft (x : A) (y : B) : f (x ⊗ₜ[R] y) = x ⊗ₜ[R[X]] y := by
    change (x ⊗ₜ[R[X]] (1 : B)) * ((1 : A) ⊗ₜ[R[X]] y) = _
    simp
  have hgt (x : A) (y : B) : g (x ⊗ₜ[R[X]] y) = q (x ⊗ₜ[R] y) := by
    change q (x ⊗ₜ[R] (1 : B)) * q ((1 : A) ⊗ₜ[R] y) = _
    rw [← map_mul]
    apply congrArg q
    change (x ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] y) = x ⊗ₜ[R] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : I ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    rintro z rfl
    change f (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b) = 0
    rw [map_sub, hft, hft]
    apply sub_eq_zero.mpr
    change (algebraMap R[X] A X) ⊗ₜ[R[X]] (1 : B) =
      (1 : A) ⊗ₜ[R[X]] (algebraMap R[X] B X)
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let fq : Q →ₐ[R] D := Ideal.Quotient.liftₐ I f hf
  have hfq (t : T) : fq (q t) = f t := rfl
  have hgf : g.comp fq = AlgHom.id R Q := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro t
    change g (fq (q t)) = q t
    rw [hfq]
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hft, hgt]
  have hfg : fq.comp g = AlgHom.id R D := by
    apply AlgHom.ext
    intro t
    change fq (g t) = t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hgt, hfq, hft]
  let e := AlgEquiv.ofAlgHom fq g hfg hgf
  let eA : Q ≃ₐ[A] D :=
    { e.toRingEquiv with
      commutes' := by
        intro z
        change fq (q (z ⊗ₜ[R] (1 : B))) = z ⊗ₜ[R[X]] (1 : B)
        rw [hfq, hft] }
  refine ⟨eA, ?_⟩
  intro x y
  change fq (q (x ⊗ₜ[R] y)) = x ⊗ₜ[R[X]] y
  rw [hfq, hft]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem hyperplane_specialization_equiv {R K A σ : Type*}
    [CommRing R] [CommRing K] [CommRing A] [Fintype σ]
    [Algebra R K] [Algebra R A]
    [Algebra (MvPolynomial σ R) K] [IsScalarTower R (MvPolynomial σ R) K]
    [Algebra (MvPolynomial σ R)[X] K]
    [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ R)[X] K] (v : σ → A) :
    let := hyperplaneFamilyAlgebra (K := R) v
    Nonempty ((K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A) ≃ₐ[K]
      ((K ⊗[R] A) ⧸ Ideal.span {algebraMap (MvPolynomial σ R)[X] K X ⊗ₜ[R] (1 : A) -
        ∑ i, (algebraMap (MvPolynomial σ R) K (MvPolynomial.X i)) ⊗ₜ[R] v i})) := by
  classical
  let := hyperplaneFamilyAlgebra (K := R) v
  let := hyperplaneFamilyAlgebra_tower (K := R) v
  let α := fun i => algebraMap (MvPolynomial σ R) K (MvPolynomial.X i)
  let β := algebraMap (MvPolynomial σ R)[X] K X
  let T := K ⊗[MvPolynomial σ R] MvPolynomial σ A
  let D := K ⊗[R] A
  let q := homogeneousLinearForm v
  let I : Ideal T := Ideal.span {β ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A) -
    (1 : K) ⊗ₜ[MvPolynomial σ R] q}
  let J : Ideal D := Ideal.span {β ⊗ₜ[R] (1 : A) - ∑ i, α i ⊗ₜ[R] v i}
  obtain ⟨e, heC, heX⟩ := mvPolynomial_parameter_tensor (R := R) (K := K) (A := A) (σ := σ)
  have he1 (k : K) : e (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) =
      k ⊗ₜ[R] (1 : A) := by
    simpa only [map_one] using heC k 1
  have het (i : σ) : e ((1 : K) ⊗ₜ[MvPolynomial σ R]
      (MvPolynomial.C (v i) * MvPolynomial.X i)) = α i ⊗ₜ[R] v i := by
    have hq : (1 : K) ⊗ₜ[MvPolynomial σ R] (MvPolynomial.C (v i) * MvPolynomial.X i) =
        ((1 : K) ⊗ₜ[MvPolynomial σ R] MvPolynomial.C (v i)) *
        ((1 : K) ⊗ₜ[MvPolynomial σ R] MvPolynomial.X i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hq, map_mul, heC, heX]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have heq : e ((1 : K) ⊗ₜ[MvPolynomial σ R] q) = ∑ i, α i ⊗ₜ[R] v i := by
    change e ((1 : K) ⊗ₜ[MvPolynomial σ R]
      (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i)) = _
    rw [TensorProduct.tmul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => het i
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {_} = (Ideal.span {_}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    change _ = {e (β ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A) -
      (1 : K) ⊗ₜ[MvPolynomial σ R] q)}
    rw [map_sub, he1, heq]
  obtain ⟨f, _⟩ := tensor_base_polynomial_relation (R := MvPolynomial σ R)
    (A := K) (B := MvPolynomial σ A)
  have hf : Nonempty ((T ⧸ I) ≃ₐ[K] (K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A)) := by
    apply Nonempty.intro
    have hqmap : algebraMap (MvPolynomial σ R)[X] (MvPolynomial σ A) X = q := by
      change (aeval (R := MvPolynomial σ R) q) X = q
      exact aeval_X q
    rw [hqmap] at f
    exact f
  obtain ⟨f⟩ := hf
  exact ⟨f.symm.trans (Ideal.quotientEquivAlg I J e hIJ)⟩
end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
