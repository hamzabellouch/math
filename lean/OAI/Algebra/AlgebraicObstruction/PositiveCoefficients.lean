import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorDifferential

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {A B α : Type*} [CommRing A] [CommRing B]

lemma reduction_map (f : A →+* B) (q : ℕ) (hq : 1 ≤ q) (x : Ring A α q) :
    reduction B α q hq (map f q x) = f (reduction A α q hq x) := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  rw [map_mk,reduction_mk,reduction_mk]
  exact MvPolynomial.constantCoeff_map f p

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]
  [Algebra.FormallySmooth (MvPolynomial α K) A]

lemma fullTaylor_map_le_nil (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    (I.map (algebraMap A (AdicCompletion J A))).map
      (fullTaylor (K := K) (α := α) I J q hq) ≤
      TaylorTarget.nilIdeal
        ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q := by
  rw [← TaylorTarget.reduction_ker _ _ q hq,
    Ideal.map_le_iff_le_comap,Ideal.map_le_iff_le_comap]
  intro a ha
  change TaylorTarget.reduction _ α q hq
    (fullTaylor (K := K) (α := α) I J q hq (AdicCompletion.of J A a)) = 0
  rw [fullTaylor_of,TaylorTarget.reduction_map,reduction_taylor,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha,map_zero]

theorem fullTaylor_pow_zero (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion J A) (hb : b ∈ (I.map (algebraMap A (AdicCompletion J A)))^q) :
    fullTaylor (K := K) (α := α) I J q hq b = 0 := by
  have hh := Ideal.mem_map_of_mem (fullTaylor (K := K) (α := α) I J q hq) hb
  rw [Ideal.map_pow] at hh
  have ht := (pow_le_pow_left' (fullTaylor_map_le_nil (K := K) (α := α) I J q hq) q) hh
  rw [TaylorTarget.variables_pow,Ideal.mem_bot] at ht
  exact ht

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {K R S α : Type*} [Field K] [CharZero K] [CommRing R] [CommRing S]
  [Algebra K R]

include K in

theorem positive_coefficient_descends (f : R →+* S) (q : ℕ) (x : Ring S α (q+1))
    (h : ∀ i : α, ∃ y : Ring R α q, shiftDeriv i q x = map f q y)
    (e : α →₀ ℕ) (he : e.degree < q+1) (he0 : e ≠ 0) :
    ∃ r : R, f r = coefficient (q+1) e x := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hh
    apply he0
    ext j
    exact not_not.mp (fun hn ↦ hh ⟨j,hn⟩)
  let d := e - Finsupp.single i 1
  have hd : d + Finsupp.single i 1 = e :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
  have hdeg : d.degree < q := by
    have hh := congrArg Finsupp.degree hd
    simp only [map_add,Finsupp.degree_single] at hh
    omega
  obtain ⟨y,hy⟩ := h i
  have hc := coefficient_shiftDeriv i q d hdeg x
  rw [hy,coefficient_map _ q d hdeg,hd] at hc
  have hu : IsUnit ((d i + 1 : ℕ) : R) := by
    have hk : IsUnit ((d i + 1 : ℕ) : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa only [map_natCast] using hk.map (algebraMap K R)
  obtain ⟨u,hu⟩ := hu
  have hfu : f (u : R) = (d i : S)+1 := by
    rw [hu,map_natCast,Nat.cast_add,Nat.cast_one]
  refine ⟨coefficient q d y * (↑(u⁻¹) : R),?_⟩
  rw [map_mul,hc,← hfu,mul_assoc,← map_mul]
  simp

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]
  [Algebra.FormallySmooth (MvPolynomial α K) A]

lemma fullTaylor_eq_of_sub_mem (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (b c : AdicCompletion J A)
    (h : b-c ∈ (I.map (algebraMap A (AdicCompletion J A)))^q) :
    fullTaylor (K := K) (α := α) I J q hq b = fullTaylor (K := K) (α := α) I J q hq c := by
  apply sub_eq_zero.mp
  exact ((fullTaylor (K := K) (α := α) I J q hq).map_sub b c).symm.trans
    (fullTaylor_pow_zero I J q hq (b-c) h)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

theorem fullTaylor_gradient_descends (E : AffineEtaleChart K α)
    (I L : Ideal E.LocalRing) (hLI : L ≤ I) (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (h : ∀ i : α, ∃ a : E.LocalRing,
      E.completionDeriv i b - AdicCompletion.of _ _ a ∈
        (L.map (algebraMap E.LocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)))^q) :
    ∀ i : α, ∃ y : TaylorShift.Target (α := α) I q,
      TaylorTarget.shiftDeriv i q
        (TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
          (q+1) (by omega) b) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient
        (S := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) I) q y := by
  intro i
  obtain ⟨a,ha⟩ := h i
  refine ⟨TaylorShift.taylor (K := K) (α := α) I q hq a,?_⟩
  rw [E.fullTaylor_deriv I i q hq]
  calc
    _ = TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
        q hq (AdicCompletion.of _ _ a) := by
      apply TaylorShift.fullTaylor_eq_of_sub_mem
      exact (pow_le_pow_left' (Ideal.map_mono hLI) q) ha
    _ = _ := TaylorShift.fullTaylor_of I (IsLocalRing.maximalIdeal E.LocalRing) q hq a

theorem fullTaylor_positive_coefficients [CharZero K] (E : AffineEtaleChart K α)
    (I L : Ideal E.LocalRing) (hLI : L ≤ I) (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (h : ∀ i : α, ∃ a : E.LocalRing,
      E.completionDeriv i b - AdicCompletion.of _ _ a ∈
        (L.map (algebraMap E.LocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)))^q)
    (e : α →₀ ℕ) (he : e.degree < q+1) (he0 : e ≠ 0) :
    ∃ a : E.LocalRing ⧸ I,
      TaylorTarget.quotientCoefficient
        (S := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) I a =
      TaylorTarget.coefficient (q+1) e
        (TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
          (q+1) (by omega) b) := by
  exact TaylorTarget.positive_coefficient_descends (K := K) _ q _
    (E.fullTaylor_gradient_descends I L hLI q hq b h) e he he0

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {A R α : Type*} [CommRing A] [CommRing R] [Algebra A R]

lemma reduction_comp_coefficient (q : ℕ) (hq : 1 ≤ q) :
    (reduction R α q hq).comp (algebraMap A (Ring R α q)) = algebraMap A R := by
  ext a
  change reduction R α q hq (mk R α q (MvPolynomial.C (algebraMap A R a))) = _
  rw [reduction_mk,MvPolynomial.constantCoeff_C]

lemma reduction_mem_coeff_pow (J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (N : ℕ)
    (x : Ring R α q) (hx : x ∈ (J.map (algebraMap A (Ring R α q)))^N) :
    reduction R α q hq x ∈ (J.map (algebraMap A R))^N := by
  have h := Ideal.mem_map_of_mem (reduction R α q hq) hx
  rwa [Ideal.map_pow,Ideal.map_map,reduction_comp_coefficient] at h

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {A R : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [Algebra A R] [Module.Finite A R]

lemma finite_algebra_adic_separated (x y : R)
    (h : ∀ N, x-y ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A R))^N) : x=y := by
  apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)).mpr
  intro N
  rw [SModEq.sub_mem,Ideal.smul_top_eq_map,Submodule.restrictScalars_mem,Ideal.map_pow]
  exact h N

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

theorem reduction_fullTaylor (E : AffineEtaleChart K α) (I : Ideal E.LocalRing)
    (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :
    TaylorTarget.reduction _ α q hq
      (TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing) q hq b) =
    Ideal.Quotient.mk (I.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))) b := by
  let J := IsLocalRing.maximalIdeal E.LocalRing
  let B := AdicCompletion J E.LocalRing
  let I' := I.map (algebraMap E.LocalRing B)
  let R := B ⧸ I'
  let m := IsLocalRing.maximalIdeal B
  let F := (TaylorTarget.reduction R α q hq).toAddMonoidHom.comp
    (TaylorShift.fullTaylor (K := K) (α := α) I J q hq).toAddMonoidHom
  let G := (Ideal.Quotient.mk I').toAddMonoidHom
  have hm : m = J.map (algebraMap E.LocalRing B) := AdicCompletion.maximalIdeal_eq_map
  apply additive_eq_of_approximation (AdicCompletion.of J E.LocalRing).toAddMonoidHom
    F G m (m.map (algebraMap B R)) q
  · intro b N
    rw [hm]
    exact completion_approximate J b N
  · exact fun x y h ↦ finite_algebra_adic_separated (A := B) x y h
  · intro N x hx
    change TaylorTarget.reduction R α q hq
      (TaylorShift.fullTaylor (K := K) (α := α) I J q hq x) ∈ _
    apply TaylorTarget.reduction_mem_coeff_pow
    rw [hm] at hx ⊢
    apply TaylorShift.fullTaylor_mem_pow (K := K) (α := α) I J q hq N x
    exact (Ideal.pow_le_pow_right (by omega)) hx
  · intro N x hx
    change Ideal.Quotient.mk I' x ∈ _
    have hx' : x ∈ m^N := (Ideal.pow_le_pow_right (by omega)) hx
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I') hx'
    have hmap : algebraMap B R = Ideal.Quotient.mk I' := rfl
    rw [hmap]
    simpa only [Ideal.map_pow] using h
  · intro a
    dsimp only [F,G,AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe]
    change TaylorTarget.reduction R α q hq
      (TaylorShift.fullTaylor (K := K) (α := α) I J q hq (AdicCompletion.of J E.LocalRing a)) =
      Ideal.Quotient.mk I' (AdicCompletion.of J E.LocalRing a)
    rw [TaylorShift.fullTaylor_of,TaylorTarget.reduction_map,TaylorShift.reduction_taylor]
    rfl

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
