import OAI.Algebra.AffineCancellation.RationalSlice

namespace OAI

noncomputable section

namespace ComplexCancellation.DifferentialSlice
variable {k K : Type*} [CommRing k] [Field K] [CharZero K] [Algebra k K]
def constantMap (D : Derivation k K K) : k →+* constants D where
  toFun a := ⟨algebraMap k K a,Derivation.map_algebraMap D a⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_one' := by apply Subtype.ext; exact map_one _
  map_add' a b := by apply Subtype.ext; exact map_add _ a b
  map_mul' a b := by apply Subtype.ext; exact map_mul _ a b
instance constantAlgebra (D : Derivation k K K) : Algebra k (constants D) := (constantMap D).toAlgebra
instance constantTower (D : Derivation k K K) : IsScalarTower k (constants D) K :=
  IsScalarTower.of_algebraMap_eq' rfl
end ComplexCancellation.DifferentialSlice

namespace ComplexCancellation.InvariantClearing
variable {k R S : Type*} [CommRing k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra k S]
def subalgebra (f : R →ₐ[k] S) (D : Derivation k R R) : Subalgebra k S where
  carrier := {s | ∃ c r : R, D c=0 ∧ c ≠ 0 ∧ f c*s=f r}
  algebraMap_mem' a := ⟨1,algebraMap k R a,D.map_one_eq_zero,one_ne_zero,by rw [map_one,one_mul,f.commutes]⟩
  add_mem' := by
    rintro s t ⟨c,r,hc,hcn,hcr⟩ ⟨d,u,hd,hdn,hdu⟩
    refine ⟨c*d,d*r+c*u,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · rw [map_mul,mul_add,map_add,map_mul,map_mul]
      calc f c*f d*s+f c*f d*t = f d*(f c*s)+f c*(f d*t) := by ring
        _ = _ := by rw [hcr,hdu]
  mul_mem' := by
    rintro s t ⟨c,r,hc,hcn,hcr⟩ ⟨d,u,hd,hdn,hdu⟩
    refine ⟨c*d,r*u,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · rw [map_mul,map_mul,show f c*f d*(s*t)=(f c*s)*(f d*t) by ring,hcr,hdu]
lemma image_mem (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) : f r ∈ subalgebra f D :=
  ⟨1,r,D.map_one_eq_zero,one_ne_zero,by rw [map_one,one_mul]⟩
end ComplexCancellation.InvariantClearing

namespace ComplexCancellation.PolynomialModel
open Polynomial DifferentialSlice FractionDerivation
variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [CharZero R] [Algebra k R]
abbrev K := FractionRing R
variable (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
abbrev F := constants (extend (K := K (R := R)) D)
def ι : R →ₐ[k] K (R := R) := IsScalarTower.toAlgHom k R (K (R := R))
include hD in
omit [IsDomain R] [CharZero R] in
lemma local_slice (hn : D ≠ 0) : ∃ s : R, D s ≠ 0 ∧ D (D s)=0 := by
  obtain ⟨r,hr⟩ : ∃ r, D r ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    ext r
    exact h r
  obtain ⟨n,hn,hdn⟩ := RationalSlice.last_nonzero D hr (hD (D r))
  refine ⟨(D : R → R)^[n] r,?_,?_⟩
  · simpa only [← Function.iterate_succ_apply',Function.iterate_succ_apply] using hn
  · simpa only [← Function.iterate_succ_apply',Function.iterate_succ_apply] using hdn
variable {t : K (R := R)} (ht : extend D t=1)
def evaluation : Polynomial (F D) →ₐ[k] K (R := R) := (aeval t).restrictScalars k
include ht in
lemma evaluation_injective : Function.Injective (evaluation (D := D) (t := t)) := eval_injective _ ht
include hD ht in
lemma exists_model (r : R) : ∃ p : Polynomial (F D), evaluation (D := D) (t := t) p=ι (k := k) r :=
  RationalSlice.image_is_polynomial D hD ht r

def model : R →ₐ[k] Polynomial (F D) where
  toFun r := Classical.choose (exists_model D hD ht r)
  map_zero' := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht 0),map_zero,map_zero]
  map_one' := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht 1),map_one,map_one]
  map_add' r s := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (r+s)),map_add,map_add,
      Classical.choose_spec (exists_model D hD ht r),Classical.choose_spec (exists_model D hD ht s)]
  map_mul' r s := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (r*s)),map_mul,map_mul,
      Classical.choose_spec (exists_model D hD ht r),Classical.choose_spec (exists_model D hD ht s)]
  commutes' a := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (algebraMap k R a)),AlgHom.commutes,AlgHom.commutes]
lemma evaluation_model (r : R) : evaluation (D := D) (t := t) (model D hD ht r)=ι (k := k) r :=
  Classical.choose_spec (exists_model D hD ht r)
lemma model_injective : Function.Injective (model D hD ht) := by
  intro r s he
  have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
  apply hi
  have h := congrArg (evaluation (D := D) (t := t)) he
  simpa only [evaluation_model] using h
lemma derivative_model (r : R) : (model D hD ht r).derivative=model D hD ht (D r) := by
  apply evaluation_injective D ht
  change aeval t (model D hD ht r).derivative = evaluation (D := D) (t := t) _
  rw [← derivative_eval _ ht]
  change extend D (evaluation (D := D) (t := t) (model D hD ht r)) = evaluation (D := D) (t := t) _
  rw [evaluation_model,evaluation_model]
  exact extend_algebraMap D r
lemma clear_constant (c : F D) : C c ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  obtain ⟨a,b,ha,hb,hbn,hab⟩ := RationalSlice.constant_fraction D hD c.property
  refine ⟨b,a,hb,hbn,?_⟩
  apply evaluation_injective D ht
  rw [map_mul,evaluation_model,evaluation_model]
  simp only [evaluation,AlgHom.restrictScalars_apply,Polynomial.aeval_C]
  change ι (k := k) b*(c : K (R := R))=ι (k := k) a
  have hn : ι (k := k) b ≠ 0 := by
    have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
    simpa only [map_zero] using hi.ne hbn
  change ι (k := k) a/ι (k := k) b=(c : K (R := R)) at hab
  rw [← hab,← mul_div_assoc,mul_div_cancel_left₀ _ hn]
lemma clear_X (s : R) (hs : D s ≠ 0) (he : D (D s)=0)
    (hsl : t=ι (k := k) s/ι (k := k) (D s)) :
    X ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  refine ⟨D s,s,he,hs,?_⟩
  apply evaluation_injective D ht
  rw [map_mul,evaluation_model,evaluation_model]
  simp only [evaluation,AlgHom.restrictScalars_apply,Polynomial.aeval_X]

  rw [hsl,← mul_div_assoc]
  apply mul_div_cancel_left₀
  have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
  simpa only [map_zero] using hi.ne hs
lemma clear_polynomial (s : R) (hs : D s ≠ 0) (he : D (D s)=0)
    (hsl : t=ι (k := k) s/ι (k := k) (D s)) (p : Polynomial (F D)) :
    p ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact add_mem hp hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact mul_mem (clear_constant D hD ht c) (pow_mem (clear_X D hD ht s hs he hsl) n)
end ComplexCancellation.PolynomialModel

end

end OAI
