import Mathlib

namespace OAI


                                             
section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

lemma linear_saturated (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) (p : R[X])
    (h : C a * X + C b ∣ C a * p) : C a * X + C b ∣ p := by
  obtain ⟨q, hq⟩ := h
  have hbq : C a ∣ C b * q := by
    refine ⟨p - X * q, ?_⟩
    linear_combination -hq
  have haq : C a ∣ q := by
    rw [C_dvd_iff_dvd_coeff] at hbq ⊢
    intro n
    apply hab
    simpa only [coeff_C_mul] using hbq n
  obtain ⟨r, rfl⟩ := haq
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ (show C a ≠ 0 by simpa using ha)
  linear_combination hq

lemma linear_pow_saturated (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) (n : ℕ) (p : R[X])
    (h : C a * X + C b ∣ (C a)^n * p) : C a * X + C b ∣ p := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply linear_saturated a b ha hab
    simpa only [pow_succ', mul_assoc] using h

theorem linear_ideal_isPrime (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    (Ideal.span {C a * X + C b} : Ideal R[X]).IsPrime := by
  let S := Localization.Away a
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors
    S (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  let M := (Submonoid.powers a).map (C : R →+* R[X])
  let : IsLocalization M S[X] := Polynomial.isLocalization _ _
  let J : Ideal R[X] := Ideal.span {C a * X + C b}
  let u : Sˣ := (IsLocalization.Away.algebraMap_isUnit (S := S) a).unit
  let z : S := -(↑u⁻¹) * algebraMap R S b
  have hu : (u : S) = algebraMap R S a := IsUnit.unit_spec _
  have he : algebraMap R[X] S[X] (C a * X + C b) =
      C (u : S) * (X - C z) := by
    change Polynomial.map (algebraMap R S) (C a * X + C b) = _
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_X]
    rw [← hu]
    rw [mul_sub, ← Polynomial.C_mul]
    have huz : (u : S) * z = -(algebraMap R S b) := by
      dsimp only [z]
      calc
        (u : S) * (-(↑u⁻¹) * algebraMap R S b) =
            -((u : S) * ↑u⁻¹) * algebraMap R S b := by ring
        _ = -(algebraMap R S b) := by simp; ring
    rw [huz, Polynomial.C_neg, sub_neg_eq_add]
  have hmap : J.map (algebraMap R[X] S[X]) = Ideal.span {X - C z} := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton, he]
    exact Ideal.span_singleton_mul_left_unit (u.isUnit.map C) _
  have hprime : (J.map (algebraMap R[X] S[X])).IsPrime := by
    rw [hmap, ← Polynomial.ker_evalRingHom]
    exact RingHom.ker_isPrime (Polynomial.evalRingHom z)
  have hcontract : (J.map (algebraMap R[X] S[X])).comap (algebraMap R[X] S[X]) = J := by
    apply le_antisymm _ Ideal.le_comap_map
    intro p hp
    obtain ⟨m, hm, hmp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S[X] J p).mp hp
    obtain ⟨r, ⟨n, rfl⟩, rfl⟩ := hm
    rw [Ideal.mem_span_singleton] at hmp ⊢
    apply linear_pow_saturated a b ha hab n p
    simpa only [map_pow] using hmp
  change J.IsPrime
  rw [← hcontract]
  exact hprime.comap _

end

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

def homogeneousLinearForm (v : σ → R) : MvPolynomial σ R :=
  ∑ i, C (v i) * X i

def separateLinearVariable (i : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) := by
  classical
  exact (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)

lemma separateLinearVariable_coeff_one (v : σ → R) (i : σ) :
    (separateLinearVariable (R := R) i (homogeneousLinearForm v)).coeff 1 = C (v i) := by
  classical
  simp only [homogeneousLinearForm, map_sum, map_mul, separateLinearVariable,
    AlgEquiv.trans_apply, renameEquiv_apply, rename_C, rename_X, optionEquivLeft_C]
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Equiv.optionSubtypeNe_symm_of_ne hji]
  · simp

lemma homogeneousLinearForm_regular_of_unit (v : σ → R) (i : σ) (hi : IsUnit (v i)) :
    homogeneousLinearForm v ∈ (MvPolynomial σ R)⁰ := by
  let e := separateLinearVariable (R := R) i
  have hreg : e (homogeneousLinearForm v) ∈ (Polynomial (MvPolynomial {j : σ // j ≠ i} R))⁰ := by
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    rw [separateLinearVariable_coeff_one]
    exact (hi.map C).mem_nonZeroDivisors
  apply mem_nonZeroDivisors_iff_right.mpr
  intro q hq
  apply e.injective
  rw [map_zero]
  apply hreg.2
  simpa only [map_mul, map_zero] using congrArg e hq

theorem homogeneousLinearForm_regular (v : σ → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    homogeneousLinearForm v ∈ (MvPolynomial σ R)⁰ := by
  classical
  apply mem_nonZeroDivisors_iff_right.mpr
  intro q hq
  have hloc (i : σ) :
      map (algebraMap R (Localization.Away (v i))) q = 0 := by
    let f : MvPolynomial σ R →+* MvPolynomial σ (Localization.Away (v i)) :=
      MvPolynomial.map (algebraMap R (Localization.Away (v i)))
    have hreg := homogeneousLinearForm_regular_of_unit
      (fun j => algebraMap R (Localization.Away (v i)) (v j)) i
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (v i)) (v i))
    apply hreg.2
    have hm := congrArg f hq
    simpa only [f, map_mul, map_zero, homogeneousLinearForm, map_sum, map_C, map_X] using hm
  ext d
  apply Localization.algebraMap_injective_of_span_eq_top (Set.range v) hv
  funext x
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨x, hx⟩ := x
  dsimp only at hi
  subst x
  have h := congrArg (fun polynomial : MvPolynomial σ (Localization.Away (v i)) =>
    polynomial.coeff d) (hloc i)
  simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    map_zero, Pi.algebraMap_apply] using h

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma separateLinearVariable_eq (v : σ → R) (i : σ) :
    separateLinearVariable (R := R) i (homogeneousLinearForm v) =
      Polynomial.C (C (v i)) * Polynomial.X +
        Polynomial.C (homogeneousLinearForm (fun j : {j : σ // j ≠ i} => v j)) := by
  classical
  simp only [homogeneousLinearForm, map_sum, map_mul]
  rw [← Equiv.sum_comp (Equiv.optionSubtypeNe i)]
  rw [Fintype.sum_option]
  simp only [separateLinearVariable, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_C, rename_X, optionEquivLeft_C, Equiv.optionSubtypeNe_symm_self,
    Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some, optionEquivLeft_X_none]
  apply congrArg (fun q : Polynomial (MvPolynomial {j : σ // j ≠ i} R) =>
    Polynomial.C (C (v i)) * Polynomial.X + q)
  apply Finset.sum_congr rfl
  intro j _
  rw [Equiv.optionSubtypeNe_symm_of_ne j.property, optionEquivLeft_X_some]

theorem homogeneousLinearForm_saturated [IsDomain R] (v : σ → R)
    (hv : Ideal.span (Set.range v) = ⊤) (a : R) (ha : a ≠ 0) (p : MvPolynomial σ R)
    (h : homogeneousLinearForm v ∣ C a * p) : homogeneousLinearForm v ∣ p := by
  classical
  let I := Ideal.span ({a} : Set R)
  let m : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hvq : Ideal.span (Set.range (fun i => m (v i))) = ⊤ := by
    have hh := congrArg (Ideal.map m) hv
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using hh
  obtain ⟨q, hq⟩ := h
  have hmapq : map m q = 0 := by
    apply (homogeneousLinearForm_regular (fun i => m (v i)) hvq).2
    have hh := congrArg (map m) hq
    have hma : m a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    simpa only [map_mul, map_C, hma, map_zero, zero_mul,
      homogeneousLinearForm, map_sum, map_X, mul_comm] using hh.symm
  have haq : C a ∣ q := by
    rw [C_dvd_iff_dvd_coeff]
    intro d
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := congrArg (fun polynomial : MvPolynomial σ (R ⧸ I) => polynomial.coeff d) hmapq
    simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using hh
  obtain ⟨r, rfl⟩ := haq
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ (show C (σ := σ) a ≠ 0 by simpa using ha)
  linear_combination hq

theorem homogeneousLinearForm_isPrime_of_unit [IsDomain R]
    (v : σ → R) (i : σ) (hi : IsUnit (v i)) :
    (Ideal.span {homogeneousLinearForm v} : Ideal (MvPolynomial σ R)).IsPrime := by
  classical
  let e := separateLinearVariable (R := R) i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {homogeneousLinearForm v}
  have ha : C (σ := {j : σ // j ≠ i}) (v i) ≠ 0 := by simpa using hi.ne_zero
  have hunit : IsUnit (C (σ := {j : σ // j ≠ i}) (v i)) := hi.map C
  have hprime : (J.map e.toRingHom).IsPrime := by
    rw [show J = Ideal.span {homogeneousLinearForm v} from rfl,
      Ideal.map_span, Set.image_singleton]
    change (Ideal.span {e (homogeneousLinearForm v)}).IsPrime
    rw [separateLinearVariable_eq]
    exact linear_ideal_isPrime _ _ ha (fun r _ => hunit.dvd)
  have hcon : (J.map e.toRingHom).comap e.toRingHom = J :=
    Ideal.comap_map_of_bijective _ e.bijective
  change J.IsPrime
  rw [← hcon]
  exact hprime.comap _

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped nonZeroDivisors
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R σ : Type*} [CommRing R] [IsDomain R] [Fintype σ]

theorem homogeneousLinearForm_isPrime (v : σ → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    (Ideal.span {homogeneousLinearForm v} : Ideal (MvPolynomial σ R)).IsPrime := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    have hh : Ideal.span (Set.range v) ≤ (⊥ : Ideal R) := by
      apply Ideal.span_le.mpr
      rintro r ⟨i, rfl⟩
      simpa using h i
    rw [hv] at hh
    exact (top_ne_bot : (⊤ : Ideal R) ≠ ⊥) (top_unique hh).symm
  obtain ⟨i, hi⟩ := hex
  let S := Localization.Away (v i)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors
    S (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hi))
  let M := (Submonoid.powers (v i)).map (C (σ := σ) : R →+* MvPolynomial σ R)
  let : IsLocalization M (MvPolynomial σ S) := MvPolynomial.isLocalization _ _
  let J : Ideal (MvPolynomial σ R) := Ideal.span {homogeneousLinearForm v}
  have hmap : J.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) =
      Ideal.span {homogeneousLinearForm (fun j => algebraMap R S (v j))} := by
    rw [show J = Ideal.span {homogeneousLinearForm v} from rfl, Ideal.map_span,
      Set.image_singleton]
    congr 2
    change MvPolynomial.map (algebraMap R S) (homogeneousLinearForm v) = _
    simp only [homogeneousLinearForm, map_sum, map_mul, map_C, map_X]
  have hprime : (J.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S))).IsPrime := by
    rw [hmap]
    exact homogeneousLinearForm_isPrime_of_unit _ i
      (IsLocalization.Away.algebraMap_isUnit (S := S) (v i))
  have hcontract : (J.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S))).comap
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) = J := by
    apply le_antisymm _ Ideal.le_comap_map
    intro p hp
    obtain ⟨m, hm, hmp⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M (MvPolynomial σ S) J p).mp hp
    obtain ⟨r, ⟨n, rfl⟩, rfl⟩ := hm
    rw [Ideal.mem_span_singleton] at hmp ⊢
    exact homogeneousLinearForm_saturated v hv ((v i)^n) (pow_ne_zero n hi) p hmp
  change J.IsPrime
  rw [← hcontract]
  exact hprime.comap _

theorem universalHyperplane_isDomain (v : σ → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    IsDomain (MvPolynomial σ R ⧸ Ideal.span {homogeneousLinearForm v}) := by
  let : (Ideal.span {homogeneousLinearForm v} : Ideal (MvPolynomial σ R)).IsPrime :=
    homogeneousLinearForm_isPrime v hv
  infer_instance

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct nonZeroDivisors

theorem flat_tensor_map_injective {R S B C : Type*}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Module.Flat R S]
    (f : B →ₐ[R] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S) f.toLinearMap hf

theorem flat_baseChange_domain_of_injective {R S B C : Type*}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Module.Flat R S]
    (f : B →ₐ[R] C) (hf : Function.Injective f) [IsDomain (S ⊗[R] C)] :
    IsDomain (S ⊗[R] B) :=
  (flat_tensor_map_injective (S := S) f hf).isDomain
    (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom

theorem geometricGeneric_domain_of_injective {R F E B C : Type*}
    [CommRing R] [Field F] [Field E] [CommRing B] [CommRing C]
    [Algebra R F] [Algebra F E] [Algebra R B] [Algebra R C] [Module.Flat R F]
    (f : B →ₐ[R] C) (hf : Function.Injective f)
    [IsDomain (E ⊗[F] (F ⊗[R] C))] : IsDomain (E ⊗[F] (F ⊗[R] B)) := by
  let g : F ⊗[R] B →ₐ[F] F ⊗[R] C :=
    Algebra.TensorProduct.map (AlgHom.id F F) f
  exact flat_baseChange_domain_of_injective g (flat_tensor_map_injective f hf)

theorem geometricGeneric_domain_of_nonempty_localization {R F E B : Type*}
    [CommRing R] [Field F] [Field E] [CommRing B] [IsDomain B]
    [Algebra R F] [Algebra F E] [Algebra R B] [Module.Flat R F]
    (s : B) (hs : s ≠ 0)
    [IsDomain (E ⊗[F] (F ⊗[R] Localization.Away s))] :
    IsDomain (E ⊗[F] (F ⊗[R] B)) := by
  apply geometricGeneric_domain_of_injective
    (IsScalarTower.toAlgHom R B (Localization.Away s))
  exact IsLocalization.injective (Localization.Away s)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hs))

end
end MaximalSeshadri.BertiniIntegral


end

end OAI
