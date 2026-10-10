import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.IdealBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {A α : Type*} [CommRing A]

theorem mk_surjective (q : ℕ) : Function.Surjective (mk A α q) :=
  Ideal.Quotient.mk_surjective

noncomputable def representative (q : ℕ) (x : Ring A α q) : MvPolynomial α A :=
  (mk_surjective q x).choose

@[simp] theorem mk_representative (q : ℕ) (x : Ring A α q) :
    mk A α q (representative q x) = x :=
  (mk_surjective q x).choose_spec

def lower (q : ℕ) : Ring A α (q+1) →+* Ring A α q :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ q))

@[simp] theorem lower_mk (q : ℕ) (p : MvPolynomial α A) :
    lower q (mk A α (q+1) p) = mk A α q p := rfl

noncomputable def shiftDeriv (i : α) (q : ℕ) (x : Ring A α (q+1)) : Ring A α q :=
  mk A α q (MvPolynomial.pderiv i (representative (q+1) x))

@[simp] theorem shiftDeriv_mk (i : α) (q : ℕ) (p : MvPolynomial α A) :
    shiftDeriv i q (mk A α (q+1) p) = mk A α q (MvPolynomial.pderiv i p) := by
  unfold shiftDeriv
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub]
  apply derivation_mem_pow (MvPolynomial.pderiv i) (variablesIdeal A α) q
  apply Ideal.Quotient.eq.mp
  exact mk_representative (q+1) (mk A α (q+1) p)

@[simp] theorem shiftDeriv_add (i : α) (q : ℕ) (x y : Ring A α (q+1)) :
    shiftDeriv i q (x+y) = shiftDeriv i q x + shiftDeriv i q y := by
  obtain ⟨x,rfl⟩ := mk_surjective (q+1) x
  obtain ⟨y,rfl⟩ := mk_surjective (q+1) y
  change shiftDeriv i q (mk A α (q+1) (x+y)) = _
  rw [shiftDeriv_mk,shiftDeriv_mk,shiftDeriv_mk]
  simp only [map_add]

@[simp] theorem shiftDeriv_one (i : α) (q : ℕ) :
    shiftDeriv (A := A) i q 1 = 0 := by
  simpa only [map_one,MvPolynomial.pderiv_one,map_zero] using
    shiftDeriv_mk i q (1 : MvPolynomial α A)

@[simp] theorem shiftDeriv_zero (i : α) (q : ℕ) :
    shiftDeriv (A := A) i q 0 = 0 := by
  simpa only [map_zero] using shiftDeriv_mk i q (0 : MvPolynomial α A)

 theorem shiftDeriv_mul (i : α) (q : ℕ) (x y : Ring A α (q+1)) :
    shiftDeriv i q (x*y) = lower q x * shiftDeriv i q y + lower q y * shiftDeriv i q x := by
  obtain ⟨x,rfl⟩ := mk_surjective (q+1) x
  obtain ⟨y,rfl⟩ := mk_surjective (q+1) y
  change shiftDeriv i q (mk A α (q+1) (x*y)) = _
  rw [shiftDeriv_mk,shiftDeriv_mk,shiftDeriv_mk,lower_mk,lower_mk]
  simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul]

 theorem shiftDeriv_C_mul (i : α) (q : ℕ) (a : A) (x : Ring A α (q+1)) :
    shiftDeriv i q (mk A α (q+1) (MvPolynomial.C a) * x) =
      mk A α q (MvPolynomial.C a) * shiftDeriv i q x := by
  rw [shiftDeriv_mul,shiftDeriv_mk,MvPolynomial.pderiv_C,map_zero,mul_zero,add_zero,lower_mk]

noncomputable def coefficient (q : ℕ) (e : α →₀ ℕ) (x : Ring A α q) : A :=
  (representative q x).coeff e

@[simp] theorem coefficient_mk (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (p : MvPolynomial α A) :
    coefficient q e (mk A α q p) = p.coeff e := by
  have hh : representative q (mk A α q p) - p ∈ variablesIdeal A α ^ q :=
    Ideal.Quotient.eq.mp (mk_representative q (mk A α q p))
  have hc : (representative q (mk A α q p) - p).coeff e = 0 := by
    by_contra hn
    exact (not_le_of_gt he) ((MvPolynomial.mem_pow_idealOfVars_iff _ _).mp hh e
      (MvPolynomial.mem_support_iff.mpr hn))
  simpa only [MvPolynomial.coeff_sub,sub_eq_zero,coefficient] using hc

 theorem coefficient_shiftDeriv (i : α) (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x : Ring A α (q+1)) :
    coefficient q e (shiftDeriv i q x) =
      coefficient (q+1) (e + Finsupp.single i 1) x * (e i + 1) := by
  obtain ⟨p,rfl⟩ := mk_surjective (q+1) x
  rw [shiftDeriv_mk,coefficient_mk q e he,MvPolynomial.coeff_pderiv,
    coefficient_mk (q+1) (e + Finsupp.single i 1) (by
      simpa only [map_add,Finsupp.degree_single] using Nat.add_lt_add_right he 1)]

 theorem coefficient_ext (q : ℕ) {x y : Ring A α q}
    (h : ∀ e, e.degree < q → coefficient q e x = coefficient q e y) : x = y := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  obtain ⟨r,rfl⟩ := mk_surjective q y
  apply Ideal.Quotient.eq.mpr
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  intro e he
  by_contra hn
  have ht : e.degree < q := by omega
  have hc := h e ht
  rw [coefficient_mk q e ht,coefficient_mk q e ht] at hc
  apply MvPolynomial.mem_support_iff.mp he
  simpa only [MvPolynomial.coeff_sub,sub_eq_zero] using hc

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {A B α : Type*} [CommRing A] [CommRing B]

lemma coefficient_map (f : A →+* B) (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x : Ring A α q) : coefficient q e (map f q x) = f (coefficient q e x) := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  rw [map_mk,coefficient_mk q e he,coefficient_mk q e he,MvPolynomial.coeff_map]

lemma coefficient_add (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x y : Ring A α q) : coefficient q e (x+y) = coefficient q e x + coefficient q e y := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  obtain ⟨r,rfl⟩ := mk_surjective q y
  rw [← map_add,coefficient_mk q e he,coefficient_mk q e he,coefficient_mk q e he,
    AddMonoidAlgebra.coeff_add,Finsupp.add_apply]

lemma coefficient_sub (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x y : Ring A α q) : coefficient q e (x-y) = coefficient q e x - coefficient q e y := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  obtain ⟨r,rfl⟩ := mk_surjective q y
  rw [← map_sub,coefficient_mk q e he,coefficient_mk q e he,coefficient_mk q e he,
    MvPolynomial.coeff_sub]

lemma coefficient_mem_map (J : Ideal A) (q : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x : Ring A α q) (hx : x ∈ J.map (algebraMap A (Ring A α q))) :
    coefficient q e x ∈ J := by
  have hle : J.map (algebraMap A (Ring A α q)) ≤
      RingHom.ker (map (Ideal.Quotient.mk J) q) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change map (Ideal.Quotient.mk J) q
      (mk A α q (MvPolynomial.C a)) = 0
    rw [map_mk,MvPolynomial.map_C,Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      MvPolynomial.C_0,map_zero]
  have hz := congrArg (coefficient q e) (hle hx)
  rw [coefficient_map _ q e he] at hz
  have h0 : coefficient q e (0 : Ring (A ⧸ J) α q) = 0 := by
    simpa only [map_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using
      coefficient_mk q e he (0 : MvPolynomial α (A ⧸ J))
  rw [h0] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

lemma coefficient_mem_pow (J : Ideal A) (q N : ℕ) (e : α →₀ ℕ) (he : e.degree < q)
    (x : Ring A α q) (hx : x ∈ (J.map (algebraMap A (Ring A α q))) ^ N) :
    coefficient q e x ∈ J ^ N := by
  apply coefficient_mem_map (J^N) q e he x
  simpa only [Ideal.map_pow] using hx

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
variable {K A α : Type*} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]

omit [IsScalarTower K (MvPolynomial α K) A] in
lemma lower_shift (I : Ideal A) (q : ℕ) (p : MvPolynomial α K) :
    TaylorTarget.lower q (shift (K := K) (α := α) I (q+1) p) = shift (K := K) (α := α) I q p := by
  have hh : (TaylorTarget.lower q).comp (shift (K := K) (α := α) I (q+1)) = shift (K := K) (α := α) I q := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [shift]
    · intro i
      simp [shift]
  exact RingHom.congr_fun hh p

lemma reduction_lower (I : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (x : Target (α := α) I (q+1)) :
    TaylorTarget.reduction (A ⧸ I) α q hq (TaylorTarget.lower q x) =
      TaylorTarget.reduction (A ⧸ I) α (q+1) (by omega) x := by
  obtain ⟨p,rfl⟩ := TaylorTarget.mk_surjective (q+1) x
  simp

lemma lower_taylor [Algebra.FormallyEtale (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (a : A) :
    TaylorTarget.lower q (taylor (K := K) (α := α) I (q+1) (by omega) a) =
      taylor (K := K) (α := α) I q hq a := by
  have hh := taylor_unique (K := K) (α := α) I q hq
    ((TaylorTarget.lower q).comp (taylor (K := K) (α := α) I (q+1) (by omega)))
    (fun p ↦ by simp only [RingHom.comp_apply,taylor_coordinates,lower_shift])
    (fun a ↦ by simp only [RingHom.comp_apply,reduction_lower,reduction_taylor])
  exact RingHom.congr_fun hh a

lemma taylor_scalar [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) (k : K) :
    taylor (K := K) (α := α) I q hq (algebraMap K A k) =
      algebraMap K (Target (α := α) I q) k := by
  have hh := taylor_coordinates (K := K) (α := α) I q hq (MvPolynomial.C k)
  have hc : algebraMap (MvPolynomial α K) A (MvPolynomial.C k) =
      algebraMap K A k := IsScalarTower.algebraMap_apply K (MvPolynomial α K) A k |>.symm
  rw [hc] at hh
  change _ = TaylorTarget.mk (A ⧸ I) α q
    (MvPolynomial.C (Ideal.Quotient.mk I (algebraMap K A k)))
  simpa only [shift, MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using hh

noncomputable def taylorAlgHom [Algebra.FormallySmooth (MvPolynomial α K) A]
    (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) : A →ₐ[K] Target (α := α) I q :=
  { taylor (K := K) (α := α) I q hq with commutes' := taylor_scalar (K := K) (α := α) I q hq }

end TaylorShift
namespace TaylorTarget
variable {K A α : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def shiftDerivLinear (i : α) (q : ℕ) :
    Ring A α (q+1) →ₗ[K] Ring A α q where
  toFun := shiftDeriv i q
  map_add' := shiftDeriv_add i q
  map_smul' k x := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def (A := Ring A α (q+1)) k x,
      Algebra.smul_def (A := Ring A α q) k (shiftDeriv i q x)]
    change shiftDeriv i q (mk A α (q+1) (MvPolynomial.C (algebraMap K A k)) * x) =
      mk A α q (MvPolynomial.C (algebraMap K A k)) * shiftDeriv i q x
    exact shiftDeriv_C_mul i q _ x

end TaylorTarget
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem completion_approximate (J : Ideal A) (b : AdicCompletion J A) (N : ℕ) :
    ∃ a : A, b - AdicCompletion.of J A a ∈
      (J.map (algebraMap A (AdicCompletion J A))) ^ N := by
  obtain ⟨a,ha⟩ := Submodule.Quotient.mk_surjective (J^N • (⊤ : Ideal A)) (b.val N)
  refine ⟨a,?_⟩
  rw [← Ideal.map_pow,← Submodule.restrictScalars_mem A,← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing]
  change AdicCompletion.eval J A N (b - AdicCompletion.of J A a) = 0
  rw [map_sub, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr ha.symm

namespace TaylorTarget
variable {R α : Type*} [CommRing R]

lemma shiftDeriv_mem_map (J : Ideal R) (i : α) (q : ℕ)
    (x : Ring R α (q+1)) (hx : x ∈ J.map (algebraMap R (Ring R α (q+1)))) :
    shiftDeriv i q x ∈ J.map (algebraMap R (Ring R α q)) := by
  have hm : x ∈ J • (⊤ : Submodule R (Ring R α (q+1))) := by
    rwa [Ideal.smul_top_eq_map,Submodule.restrictScalars_mem]
  have ht := Submodule.mem_map_of_mem (f := shiftDerivLinear (K := R) i q) hm
  rw [Submodule.map_smul''] at ht
  have hle : J • (⊤ : Submodule R (Ring R α (q+1))).map (shiftDerivLinear (K := R) i q) ≤
      J • (⊤ : Submodule R (Ring R α q)) := smul_le_smul_left J le_top
  have hh := hle ht
  rwa [Ideal.smul_top_eq_map,Submodule.restrictScalars_mem] at hh

lemma shiftDeriv_mem_pow (J : Ideal R) (i : α) (q N : ℕ)
    (x : Ring R α (q+1)) (hx : x ∈ (J.map (algebraMap R (Ring R α (q+1))))^N) :
    shiftDeriv i q x ∈ (J.map (algebraMap R (Ring R α q)))^N := by
  rw [← Ideal.map_pow] at hx ⊢
  exact shiftDeriv_mem_map (J^N) i q x hx

lemma shiftDeriv_sub (i : α) (q : ℕ) (x y : Ring R α (q+1)) :
    shiftDeriv i q (x-y) = shiftDeriv i q x - shiftDeriv i q y :=
  map_sub (shiftDerivLinear (K := R) i q) x y

variable [Algebra A R]

omit [IsNoetherianRing A] in
lemma shiftDeriv_mem_coeff_pow (J : Ideal A) (i : α) (q N : ℕ)
    (x : Ring R α (q+1)) (hx : x ∈ (J.map (algebraMap A (Ring R α (q+1))))^N) :
    shiftDeriv i q x ∈ (J.map (algebraMap A (Ring R α q)))^N := by
  have hbig : (algebraMap R (Ring R α (q+1))).comp (algebraMap A R) =
      algebraMap A (Ring R α (q+1)) := (IsScalarTower.algebraMap_eq A R _).symm
  have hsmall : (algebraMap R (Ring R α q)).comp (algebraMap A R) =
      algebraMap A (Ring R α q) := (IsScalarTower.algebraMap_eq A R _).symm
  rw [← hbig, ← Ideal.map_map] at hx
  rw [← hsmall, ← Ideal.map_map]
  exact shiftDeriv_mem_pow (J.map (algebraMap A R)) i q N x hx

end TaylorTarget
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
