import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.ChartCompletion

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
variable {K A α : Type*} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]

abbrev Target (I : Ideal A) (q : ℕ) := TaylorTarget.Ring (A ⧸ I) α q

def shift (I : Ideal A) (q : ℕ) : MvPolynomial α K →+* Target (α := α) I q :=
  MvPolynomial.eval₂Hom
    ((TaylorTarget.mk (A ⧸ I) α q).comp (MvPolynomial.C.comp
      ((Ideal.Quotient.mk I).comp (algebraMap K A))))
    (fun i ↦ TaylorTarget.mk (A ⧸ I) α q
      (MvPolynomial.C (Ideal.Quotient.mk I (algebraMap (MvPolynomial α K) A
        (MvPolynomial.X i))) + MvPolynomial.X i))

lemma reduction_shift (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (p : MvPolynomial α K) :
    TaylorTarget.reduction (A ⧸ I) α q hq (shift I q p) =
      Ideal.Quotient.mk I (algebraMap (MvPolynomial α K) A p) := by
  have hh : (TaylorTarget.reduction (A ⧸ I) α q hq).comp (shift I q) =
      (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial α K) A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [shift,RingHom.comp_apply,MvPolynomial.eval₂Hom_C,
        TaylorTarget.reduction_mk,MvPolynomial.constantCoeff_C]
      exact congrArg (Ideal.Quotient.mk I)
        (IsScalarTower.algebraMap_apply K (MvPolynomial α K) A k)
    · intro i
      simp [shift]
  exact RingHom.congr_fun hh p

noncomputable def taylor [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) : A →+* Target (α := α) I q := by
  letI : Algebra (MvPolynomial α K) (Target (α := α) I q) := (shift I q).toAlgebra
  let f : Target (α := α) I q →ₐ[MvPolynomial α K] (A ⧸ I) :=
    { TaylorTarget.reduction (A ⧸ I) α q hq with
      commutes' := reduction_shift I q hq }
  exact (Algebra.FormallySmooth.liftOfSurjective
    (Ideal.Quotient.mkₐ (MvPolynomial α K) I) f
    (TaylorTarget.reduction_surjective (A ⧸ I) α q hq)
    (by change IsNilpotent (RingHom.ker (TaylorTarget.reduction (A ⧸ I) α q hq))
        rw [TaylorTarget.reduction_ker]
        exact ⟨q,TaylorTarget.variables_pow (A ⧸ I) α q⟩)).toRingHom

lemma reduction_taylor [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (a : A) :
    TaylorTarget.reduction (A ⧸ I) α q hq (taylor (K := K) (α := α) I q hq a) =
      Ideal.Quotient.mk I a := by
  let : Algebra (MvPolynomial α K) (Target (α := α) I q) := (shift I q).toAlgebra
  let f : Target (α := α) I q →ₐ[MvPolynomial α K] (A ⧸ I) :=
    { TaylorTarget.reduction (A ⧸ I) α q hq with
      commutes' := reduction_shift I q hq }
  exact Algebra.FormallySmooth.liftOfSurjective_apply
    (Ideal.Quotient.mkₐ (MvPolynomial α K) I) f
    (TaylorTarget.reduction_surjective (A ⧸ I) α q hq)
    (by change IsNilpotent (RingHom.ker (TaylorTarget.reduction (A ⧸ I) α q hq))
        rw [TaylorTarget.reduction_ker]
        exact ⟨q,TaylorTarget.variables_pow (A ⧸ I) α q⟩) a

lemma taylor_coordinates [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (p : MvPolynomial α K) :
    taylor (K := K) (α := α) I q hq (algebraMap (MvPolynomial α K) A p) = shift I q p := by
  let : Algebra (MvPolynomial α K) (Target (α := α) I q) := (shift I q).toAlgebra
  unfold taylor
  exact AlgHom.commutes _ p

theorem taylor_finite [Algebra.FormallySmooth (MvPolynomial α K) A] [Finite α]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    @Module.Finite A (Target (α := α) I q) _ _ (taylor (K := K) (α := α) I q hq).toAlgebra.toModule := by
  let : Algebra A (Target (α := α) I q) := (taylor (K := K) (α := α) I q hq).toAlgebra
  exact TaylorTarget.finite_shifted (A ⧸ I) α A q hq (reduction_taylor (K := K) (α := α) I q hq)

lemma taylor_unique [Algebra.FormallyEtale (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (g : A →+* Target (α := α) I q)
    (hg : ∀ p : MvPolynomial α K,
      g (algebraMap (MvPolynomial α K) A p) = shift I q p)
    (hr : ∀ a, TaylorTarget.reduction (A ⧸ I) α q hq (g a) = Ideal.Quotient.mk I a) :
    g = taylor (K := K) (α := α) I q hq := by
  let : Algebra (MvPolynomial α K) (Target (α := α) I q) := (shift I q).toAlgebra
  let g' : A →ₐ[MvPolynomial α K] Target (α := α) I q := ⟨g,hg⟩
  let t' : A →ₐ[MvPolynomial α K] Target (α := α) I q :=
    ⟨taylor (K := K) (α := α) I q hq, taylor_coordinates I q hq⟩
  have hh : g' = t' := Algebra.FormallyUnramified.ext'
    (TaylorTarget.reduction (A ⧸ I) α q hq)
    (by rw [TaylorTarget.reduction_ker]
        exact ⟨q,TaylorTarget.variables_pow (A ⧸ I) α q⟩) g' t'
    (fun a ↦ (hr a).trans (reduction_taylor (K := K) (α := α) I q hq a).symm)
  exact congrArg AlgHom.toRingHom hh

def coefficient (I : Ideal A) (q : ℕ) : A →+* Target (α := α) I q :=
  (TaylorTarget.mk (A ⧸ I) α q).comp (MvPolynomial.C.comp (Ideal.Quotient.mk I))

lemma reduction_coefficient (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (a : A) :
    TaylorTarget.reduction (A ⧸ I) α q hq (coefficient I q a) = Ideal.Quotient.mk I a := by
  simp [coefficient]

lemma actions_sup_nil [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    J.map (taylor (K := K) (α := α) I q hq) ⊔ TaylorTarget.nilIdeal (A ⧸ I) α q =
    J.map (coefficient (α := α) I q) ⊔ TaylorTarget.nilIdeal (A ⧸ I) α q := by
  let r := TaylorTarget.reduction (A ⧸ I) α q hq
  have he : r.comp (taylor (K := K) (α := α) I q hq) =
      r.comp (coefficient (α := α) I q) := by
    ext a
    exact (reduction_taylor (K := K) (α := α) I q hq a).trans
      (reduction_coefficient I q hq a).symm
  have hi : (J.map (taylor (K := K) (α := α) I q hq)).map r =
      (J.map (coefficient (α := α) I q)).map r := by
    rw [Ideal.map_map,Ideal.map_map,he]
  have hc := congrArg (Ideal.comap r) hi
  simpa only [Ideal.comap_map_of_surjective r
    (TaylorTarget.reduction_surjective (A ⧸ I) α q hq),
    ← RingHom.ker_eq_comap_bot,TaylorTarget.reduction_ker,r] using hc

theorem actions_cofinal [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    (J.map (taylor (K := K) (α := α) I q hq)) ^ (N + q - 1) ≤
      (J.map (coefficient (α := α) I q)) ^ N ∧
    (J.map (coefficient (α := α) I q)) ^ (N + q - 1) ≤
      (J.map (taylor (K := K) (α := α) I q hq)) ^ N :=
  shifted_ideal_cofinal _ _ (TaylorTarget.nilIdeal (A ⧸ I) α q) q hq
    (TaylorTarget.variables_pow (A ⧸ I) α q) (actions_sup_nil I J q hq) N

end TaylorShift
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
variable {K A α : Type*} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]

noncomputable def completionEquiv [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    AdicCompletion (J.map (taylor (K := K) (α := α) I q hq)) (Target (α := α) I q) ≃+*
    AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) :=
  AdicCofinal.equiv _ _ (q-1) (q-1)
    (fun N ↦ by simpa [Nat.add_sub_assoc hq] using (actions_cofinal I J q hq N).1)
    (fun N ↦ by simpa [Nat.add_sub_assoc hq] using (actions_cofinal I J q hq N).2)

@[simp] lemma completionEquiv_of [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (x : Target (α := α) I q) :
    completionEquiv (K := K) I J q hq
      (AdicCompletion.of (J.map (taylor (K := K) (α := α) I q hq)) _ x) =
    AdicCompletion.of (J.map (coefficient (α := α) I q)) _ x :=
  AdicCofinal.equiv_of _ _ _ _ _ _ x

end TaylorShift
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
