import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.SemilocalCompletion

namespace OAI

noncomputable section
open scoped BigOperators

open scoped TensorProduct nonZeroDivisors

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

variable {R A S F KA KS : Type*}
variable [CommRing R] [IsDomain R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable [Field KA] [Field KS] [Algebra R KA] [Algebra R KS]
variable [Algebra F KA] [Algebra F KS]
variable [IsScalarTower R F KA] [IsScalarTower R F KS]

omit [IsDomain R] in
theorem reduced_tensor_of_field_embeddings [IsDomain R] [CharZero F]
    [FiniteDimensional F KS] [Module.Flat R A]
    (i : A →ₐ[R] KA) (hi : Function.Injective i)
    (j : S →ₐ[R] KS) (hj : Function.Injective j) : IsReduced (A ⊗[R] S) := by
  have : Module.Flat R F := IsLocalization.flat F R⁰
  have : Module.Flat R KS := Module.Flat.trans R F KS
  let f : A ⊗[R] S →ₐ[R] A ⊗[R] KS := Algebra.TensorProduct.map (AlgHom.id R A) j
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap hj
  let g : A ⊗[R] KS →ₐ[R] KA ⊗[R] KS := Algebra.TensorProduct.map i (AlgHom.id R KS)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap i.toLinearMap hi
  let e : KA ⊗[F] KS ≃ₐ[F] KA ⊗[R] KS :=
    IsLocalization.algebraTensorEquiv R⁰ F KA KS
  have : Algebra.FormallyUnramified F KS := Algebra.FormallyUnramified.of_isSeparable F KS
  have : Algebra.EssFiniteType F KS := inferInstance
  have : IsReduced (KA ⊗[F] KS) :=
    Algebra.FormallyUnramified.isReduced_of_field KA (KA ⊗[F] KS)
  have : IsReduced (KA ⊗[R] KS) := isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_injective (g.comp f) (hg.comp hf)

section Domains
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem reduced_flat_domain_tensor [IsDomain A] [IsDomain S] [CharZero R]
    [FaithfulSMul R A] [FaithfulSMul R S] [Module.Finite R S] [Module.Flat R A] :
    IsReduced (A ⊗[R] S) := by
  apply reduced_tensor_of_field_embeddings (F := FractionRing R)
    (IsScalarTower.toAlgHom R A (FractionRing A))
    (IsFractionRing.injective A (FractionRing A))
    (IsScalarTower.toAlgHom R S (FractionRing S))
    (IsFractionRing.injective S (FractionRing S))

end Domains
end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness
open scoped TensorProduct
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S]
  [FaithfulSMul R S] [Module.Finite R S]

theorem reduced_finite_domain_completion (p : Ideal R) [p.IsMaximal]
    [IsDomain (AdicCompletion p R)] (q : Ideal S) [q.IsMaximal]
    (hpq : p.map (algebraMap R S) ≤ q) : IsReduced (AdicCompletion q S) := by
  let J := p.map (algebraMap R S)
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : FaithfulSMul R (AdicCompletion p R) :=
    inferInstance
  have : IsReduced (AdicCompletion p R ⊗[R] S) := reduced_flat_domain_tensor
  have : IsReduced (AdicCompletion J S) :=
    isReduced_of_injective (CompletionScalar.tensorAlgEquiv (S := S) p).symm
      (CompletionScalar.tensorAlgEquiv (S := S) p).symm.injective
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (R ⧸ p) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ J)
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ p) (S ⧸ J)
  exact SemilocalCompletion.reduced_at_maximal J q hpq

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness
universe u
variable {K S : Type u} [Field K] [CharZero K] [CommRing S] [IsDomain S]
  [Algebra K S] [Algebra.FiniteType K S]

theorem reduced_domain_point_completion (e : S →ₐ[K] K) :
    IsReduced (AdicCompletion (RingHom.ker e.toRingHom) S) := by
  obtain ⟨n,f,hf,hfin⟩ := exists_finite_inj_algHom_of_fg K S
  let R := MvPolynomial (Fin n) K
  let : Algebra R S := f.toRingHom.toAlgebra
  have : Module.Finite R S := hfin
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hf
  let a : Fin n → K := fun i ↦ e (f (MvPolynomial.X i))
  let p : Ideal R := RingHom.ker (MvPolynomial.aeval a : R →ₐ[K] K).toRingHom
  have : p.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.aeval a : R →ₐ[K] K).toRingHom
    (fun k ↦ ⟨MvPolynomial.C k,by simp⟩)
  have : IsDomain (AdicCompletion p R) := PolynomialPointCompletion.isDomain_completion a
  have : (RingHom.ker e.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective e.toRingHom
    (fun k ↦ ⟨algebraMap K S k,e.commutes k⟩)
  apply reduced_finite_domain_completion p (RingHom.ker e.toRingHom)
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change e (f r) = 0
  have he : e.comp f = MvPolynomial.aeval a := MvPolynomial.aeval_unique (e.comp f)
  exact (AlgHom.congr_fun he r).trans hr

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem reduced_completion_of_quotients {ι : Type u} [Fintype ι] (J : ι → Ideal R)
    (hJ : (⨅ i,J i) = ⊥) (I : Ideal R)
    (hred : ∀ i, IsReduced (AdicCompletion (I.map (Ideal.Quotient.mk (J i))) (R ⧸ J i))) :
    IsReduced (AdicCompletion I R) := by
  classical
  let A := AdicCompletion I R
  let Q := fun i ↦ R ⧸ J i
  let f : R →ₐ[R] ∀ i,Q i := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (J i)
  have hf : Function.Injective f := by
    intro x y h
    apply sub_eq_zero.mp
    have hz : x-y ∈ (⨅ i,J i) := by
      rw [Ideal.mem_iInf]
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub]
      exact sub_eq_zero.mpr (congrFun h i)
    rwa [hJ,Ideal.mem_bot] at hz
  let g : A ⊗[R] R →ₐ[R] A ⊗[R] (∀ i,Q i) :=
    Algebra.TensorProduct.map (AlgHom.id R A) f
  have hg : Function.Injective g := Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have (i : ι) : IsReduced (A ⊗[R] Q i) := by
    have := hred i
    exact isReduced_of_injective (CompletionScalar.tensorAlgEquiv (S := Q i) I)
      (CompletionScalar.tensorAlgEquiv (S := Q i) I).injective
  let e := Algebra.TensorProduct.piRight R R A Q
  have : IsReduced (A ⊗[R] (∀ i,Q i)) := isReduced_of_injective e e.injective
  have : IsReduced (A ⊗[R] R) := isReduced_of_injective g hg
  let e' := Algebra.TensorProduct.rid R R A
  exact isReduced_of_injective e'.symm e'.symm.injective

omit [IsNoetherianRing R] in
theorem reduced_top_completion [IsNoetherianRing R] : IsReduced (AdicCompletion (⊤ : Ideal R) R) := by
  have : Subsingleton (AdicCompletion (⊤ : Ideal R) R) :=
    IsHausdorff.subsingleton (inferInstance : IsHausdorff (⊤ : Ideal R) _)
  constructor
  intro x hx
  exact Subsingleton.elim x 0

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness
universe u
variable {K S : Type u} [Field K] [CharZero K] [CommRing S] [IsReduced S]
  [Algebra K S] [Algebra.FiniteType K S]

theorem reduced_point_completion (e : S →ₐ[K] K) :
    IsReduced (AdicCompletion (RingHom.ker e.toRingHom) S) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let ι := minimalPrimes S
  let : Fintype ι := (minimalPrimes.finite_of_isNoetherianRing (R := S)).fintype
  let J : ι → Ideal S := Subtype.val
  have hJ : (⨅ i,J i) = ⊥ := by
    rw [show (⨅ i,J i) = sInf (minimalPrimes S) from
      le_antisymm (le_sInf fun Q hQ ↦ iInf_le (fun i : ι ↦ J i) ⟨Q,hQ⟩)
        (le_iInf fun i ↦ sInf_le i.property)]
    rw [Ideal.sInf_minimalPrimes]
    exact (nilradical_eq_bot_iff).mpr inferInstance
  let p := RingHom.ker e.toRingHom
  have : p.IsMaximal := RingHom.ker_isMaximal_of_surjective e.toRingHom
    (fun k ↦ ⟨algebraMap K S k,e.commutes k⟩)
  apply reduced_completion_of_quotients J hJ p
  intro q
  have : (J q).IsPrime := q.property.isPrime
  by_cases hq : J q ≤ p
  · let e' : (S ⧸ J q) →ₐ[K] K := Ideal.Quotient.liftₐ (J q) e hq
    have he' : p.map (Ideal.Quotient.mk (J q)) = RingHom.ker e'.toRingHom := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (J q)) Ideal.Quotient.mk_surjective
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hq,RingHom.comap_ker]
      rfl
    rw [he']
    exact reduced_domain_point_completion e'
  · have htop : p.map (Ideal.Quotient.mk (J q)) = ⊤ := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (J q)) Ideal.Quotient.mk_surjective
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot,Ideal.mk_ker,Ideal.comap_top]
      by_contra hne
      have he : p = p ⊔ J q := Ideal.IsMaximal.eq_of_le inferInstance hne le_sup_left
      exact hq (he ▸ le_sup_right)
    rw [htop]
    exact reduced_top_completion

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionLocalization
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S p]

noncomputable def level (n : ℕ) : R ⧸ p^n ≃+* S ⧸ (IsLocalRing.maximalIdeal S)^n :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).toRingEquiv

lemma level_factor {m n : ℕ} (h : m ≤ n) (x : R ⧸ p^n) :
    level (S := S) p m (Ideal.Quotient.factorPow p h x) =
      Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) h (level p n x) := by
  induction x using Quotient.inductionOn' with
  | _ r => rfl

noncomputable def family (n : ℕ) :
    AdicCompletion p R →+* S ⧸ (IsLocalRing.maximalIdeal S)^n :=
  (level p n).toRingHom.comp (AdicCompletion.evalₐ p n).toRingHom

lemma compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) h).comp (family p n) =
      family p m := by
  ext x
  change Ideal.Quotient.factorPow _ h (level p n (AdicCompletion.evalₐ p n x)) =
    level p m (AdicCompletion.evalₐ p m x)
  rw [← level_factor,AdicCofinal.factor_eval]

noncomputable def forward : AdicCompletion p R →+* AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  AdicCompletion.liftRingHom _ (family p) (compatible p)

lemma eval_forward (n : ℕ) (x : AdicCompletion p R) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n (forward p x) =
      level p n (AdicCompletion.evalₐ p n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (compatible p) n x

noncomputable def inverseFamily (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal S) S →+* R ⧸ p^n :=
  (level p n).symm.toRingHom.comp (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n).toRingHom

lemma inverse_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow p h).comp (inverseFamily (S := S) p n) =
      inverseFamily p m := by
  ext x
  apply (level (S := S) p m).injective
  change level p m (Ideal.Quotient.factorPow p h
    ((level p n).symm (AdicCompletion.evalₐ _ n x))) =
    level p m ((level p m).symm (AdicCompletion.evalₐ _ m x))
  rw [level_factor,RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  exact AdicCofinal.factor_eval _ h x

noncomputable def inverse : AdicCompletion (IsLocalRing.maximalIdeal S) S →+* AdicCompletion p R :=
  AdicCompletion.liftRingHom p (inverseFamily p) (inverse_compatible p)

lemma eval_inverse (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal S) S) :
    AdicCompletion.evalₐ p n (inverse p x) =
      (level p n).symm (AdicCompletion.evalₐ _ n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (inverse_compatible p) n x

noncomputable def equiv :
    AdicCompletion p R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  { forward p with
    invFun := inverse p
    left_inv := fun x ↦ by
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ p n (inverse p (forward p x)) = _
      rw [eval_inverse,eval_forward,RingEquiv.symm_apply_apply]
    right_inv := fun x ↦ by
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ _ n (forward p (inverse p x)) = _
      rw [eval_forward,eval_inverse,RingEquiv.apply_symm_apply] }

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionLocalization

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionLocalization
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S p]
@[simp] lemma equiv_of (r : R) :
    equiv (S := S) p (AdicCompletion.of p R r) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n (forward p _) = _
  rw [eval_forward, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl
end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionLocalization

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness
universe u
variable {K R : Type u} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Algebra.FiniteType K R]

theorem radical_map_completion (e : R →ₐ[K] K) (I : Ideal R)
    (hI : I.IsRadical) (hIp : I ≤ RingHom.ker e.toRingHom) :
    (I.map (algebraMap R (AdicCompletion (RingHom.ker e.toRingHom) R))).IsRadical := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  let p := RingHom.ker e.toRingHom
  let e' : (R ⧸ I) →ₐ[K] K := Ideal.Quotient.liftₐ I e hIp
  have he' : p.map (Ideal.Quotient.mk I) = RingHom.ker e'.toRingHom := by
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp,RingHom.comap_ker]
    rfl
  have : IsReduced (AdicCompletion (p.map (Ideal.Quotient.mk I)) (R ⧸ I)) := by
    rw [he']
    exact reduced_point_completion e'
  have : IsReduced (TensorProduct R (AdicCompletion p R) (R ⧸ I)) :=
    isReduced_of_injective (CompletionScalar.tensorAlgEquiv (S := R ⧸ I) p)
      (CompletionScalar.tensorAlgEquiv (S := R ⧸ I) p).injective
  let q := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion p R) I
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr (isReduced_of_injective q q.injective)

instance rationalPointPrime (e : R →ₐ[K] K) : (RingHom.ker e.toRingHom).IsPrime :=
  RingHom.ker_isPrime _

lemma radical_local_completion_transfer (e : R →ₐ[K] K)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsLocalization.AtPrime A (RingHom.ker e.toRingHom)]
    (I : Ideal A) (hI : I.IsRadical) (hIne : I ≠ ⊤)
    (q : AdicCompletion (RingHom.ker e.toRingHom) R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal A) A)
    (hq : q.toRingHom.comp (algebraMap R (AdicCompletion (RingHom.ker e.toRingHom) R)) =
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)).comp (algebraMap R A)) :
    (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))).IsRadical := by
  let p := RingHom.ker e.toRingHom
  let J := I.comap (algebraMap R A)
  have hJ : J.IsRadical := hI.comap _
  have hJp : J ≤ p := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal A p]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hIne)
  have hJmap : J.map (algebraMap R A) = I := IsLocalization.map_under p.primeCompl A I
  have heq : (J.map (algebraMap R (AdicCompletion p R))).map q.toRingHom =
      I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    rw [Ideal.map_map,hq,← Ideal.map_map,hJmap]
  rw [← heq]
  have he := Ideal.map_comap_of_equiv (I := J.map (algebraMap R (AdicCompletion p R))) q
  change (J.map (algebraMap R (AdicCompletion p R))).map q.toRingHom = _ at he
  rw [he]
  exact (radical_map_completion e J hJ hJp).comap _

theorem radical_local_completion (e : R →ₐ[K] K)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsLocalization.AtPrime A (RingHom.ker e.toRingHom)]
    (I : Ideal A) (hI : I.IsRadical) (hIne : I ≠ ⊤) :
    (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))).IsRadical := by
  let p := RingHom.ker e.toRingHom
  have : p.IsMaximal := RingHom.ker_isMaximal_of_surjective e.toRingHom
    (fun k ↦ ⟨algebraMap K R k,e.commutes k⟩)
  apply radical_local_completion_transfer e A I hI hIne (CompletionLocalization.equiv (S := A) p)
  apply RingHom.ext
  intro r
  exact CompletionLocalization.equiv_of (S := A) p r
end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness

end

end OAI
