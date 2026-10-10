import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.MonicSMulRegularQuotientMapC

namespace OAI

namespace SiegelZeros

open Polynomial
open Ideal RingTheory.Sequence IsLocalRing
open Ideal RingTheory.Sequence
open scoped Pointwise
open Ideal RingTheory.Sequence
open CategoryTheory Abelian
universe u
open scoped BigOperators
namespace WeightedTorusJets

theorem isRegular_parameters_mvPolynomial_localization
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (fs : List (Localization.AtPrime p))
    (hrad : (Ideal.ofList fs).radical = IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (fs.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime p) fs := by
  exact isRegular_parameters_of_exists_regular_maximal_generators
    (exists_regular_maximal_generators_mvPolynomial_localization K σ p) fs hrad hlen

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

theorem localRingHom_surjective_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    Function.Surjective (Localization.localRingHom (p.comap f) p f rfl) := by
  have : IsLocalization ((p.comap f).primeCompl.map f) (Localization.AtPrime p) := by
    rw [p.map_primeCompl_comap_of_surjective f hf]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (p.comap f).primeCompl
    (Localization.AtPrime (p.comap f)) (Localization.AtPrime p) (g := f) hf

theorem ker_localRingHom_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    RingHom.ker (Localization.localRingHom (p.comap f) p f rfl) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (p.comap f))) := by
  exact IsLocalization.ker_map (Localization.AtPrime p) f
    (p.map_primeCompl_comap_of_surjective f hf)

noncomputable def localQuotientEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    (Localization.AtPrime (p.comap f) ⧸
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (p.comap f)))) ≃+*
        Localization.AtPrime p :=
  (Ideal.quotEquivOfEq (ker_localRingHom_of_surjective f hf p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (localRingHom_surjective_of_surjective f hf p))

theorem localQuotientEquiv_apply_mk_algebraMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] (x : R) :
    localQuotientEquiv f hf p (Ideal.Quotient.mk _
      (algebraMap R (Localization.AtPrime (p.comap f)) x)) =
        algebraMap S (Localization.AtPrime p) (f x) := by
  simp only [localQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, Localization.localRingHom_to_map]

noncomputable def localQuotientAlgEquiv
    {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    (Localization.AtPrime (p.comap f.toRingHom) ⧸
      (RingHom.ker f.toRingHom).map
        (algebraMap R (Localization.AtPrime (p.comap f.toRingHom)))) ≃ₐ[K]
          Localization.AtPrime p :=
  (Ideal.quotientEquivAlgOfEq K (ker_localRingHom_of_surjective f.toRingHom hf p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Localization.localAlgHom (p.comap f.toRingHom) p f rfl)
      (localRingHom_surjective_of_surjective f.toRingHom hf p))

theorem localQuotientAlgEquiv_apply_mk_algebraMap
    {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] (x : R) :
    localQuotientAlgEquiv f hf p (Ideal.Quotient.mk _
      (algebraMap R (Localization.AtPrime (p.comap f.toRingHom)) x)) =
        algebraMap S (Localization.AtPrime p) (f x) := by
  exact localQuotientEquiv_apply_mk_algebraMap f.toRingHom hf p x

open Polynomial

theorem ker_mvPolynomial_evaluation
    {R σ : Type*} [CommRing R] (a : R) :
    RingHom.ker (MvPolynomial.map (σ := σ) (evalRingHom a) :
      MvPolynomial σ R[X] →+* MvPolynomial σ R) =
        Ideal.span {MvPolynomial.C (σ := σ) (X - C a)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (MvPolynomial.C_dvd_iff_map_hom_eq_zero (evalRingHom a) (X - C a)
    (fun _ => dvd_iff_isRoot.symm) f).symm

noncomputable def mvPolynomialLocalQuotientAlgEquiv
    {R σ : Type*} [CommRing R] (p : Ideal (MvPolynomial σ R)) [p.IsPrime] (a : R) :
    letI : CommRing (Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := inferInstance
    (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))) ⧸
      (Ideal.span {algebraMap (MvPolynomial σ R[X])
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
          (MvPolynomial.C (σ := σ) (X - C a))} :
        Ideal (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))))
          ≃ₐ[R] Localization.AtPrime p := by
  letI : CommRing (Localization.AtPrime
    (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := inferInstance
  have h : (Ideal.span {algebraMap (MvPolynomial σ R[X])
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (MvPolynomial.C (σ := σ) (X - C a))} :
          Ideal (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))) =
      (RingHom.ker (MvPolynomial.map (σ := σ) (evalRingHom a))).map
        (algebraMap (MvPolynomial σ R[X])
          (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))) := by
    rw [ker_mvPolynomial_evaluation, Ideal.map_span]
    simp
  exact (Ideal.quotientEquivAlgOfEq R h).trans
    (localQuotientAlgEquiv (MvPolynomial.mapAlgHom (aeval a))
      (MvPolynomial.map_surjective _ (fun r => ⟨C r, eval_C⟩)) p)

theorem mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap
    {R σ : Type*} [CommRing R] (p : Ideal (MvPolynomial σ R)) [p.IsPrime] (a : R)
    (f : MvPolynomial σ R[X]) :
    mvPolynomialLocalQuotientAlgEquiv p a (Ideal.Quotient.mk _
      (algebraMap (MvPolynomial σ R[X])
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) f)) =
      algebraMap (MvPolynomial σ R) (Localization.AtPrime p) (MvPolynomial.map (evalRingHom a) f) := by
  exact localQuotientAlgEquiv_apply_mk_algebraMap (MvPolynomial.mapAlgHom (aeval a))
    (MvPolynomial.map_surjective _ (fun r => ⟨C r, eval_C⟩)) p f

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

noncomputable def quotientFamilySpecializationAlgEquiv
    {K S R ι : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (J : Ideal S) (e : (S ⧸ J) ≃ₐ[K] R)
    (f : ι → S) (g : ι → R)
    (hfg : ∀ i, e (Ideal.Quotient.mk J (f i)) = g i) :
    ((S ⧸ Ideal.span (Set.range f)) ⧸
      J.map (Ideal.Quotient.mk (Ideal.span (Set.range f)))) ≃ₐ[K]
      R ⧸ Ideal.span (Set.range g) := by
  refine (DoubleQuot.quotQuotEquivCommₐ K (Ideal.span (Set.range f)) J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span (Set.range g) =
    ((Ideal.span (Set.range f)).map (Ideal.Quotient.mk J)).map e.toRingEquiv.toRingHom
  rw [Ideal.map_map, Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, RingHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, hfg i⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, (hfg i).symm.trans h⟩

theorem isRegular_quotient_iff
    {K S R : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (J : Ideal S) (e : (S ⧸ J) ≃ₐ[K] R) (fs : List S) :
    RingTheory.Sequence.IsRegular (S ⧸ J) fs ↔
      RingTheory.Sequence.IsRegular R (fs.map (fun x => e (Ideal.Quotient.mk J x))) := by
  apply e.toAddEquiv.isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  change e ((Ideal.Quotient.mk J r) * x) = e (Ideal.Quotient.mk J r) * e x
  exact e.map_mul _ _

theorem isRegular_quotSMulTop_iff
    {K S R : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (t : S) (e : (S ⧸ Ideal.span {t}) ≃ₐ[K] R) (fs : List S) :
    RingTheory.Sequence.IsRegular (QuotSMulTop t S) fs ↔
      RingTheory.Sequence.IsRegular R
        (fs.map (fun x => e (Ideal.Quotient.mk (Ideal.span {t}) x))) :=
  ((QuotSMulTop.equivQuotTensor t S ≪≫ₗ TensorProduct.rid S (S ⧸ Ideal.span {t})).isRegular_congr fs).trans
    (isRegular_quotient_iff (Ideal.span {t}) e fs)



open Polynomial

theorem isRegular_mvPolynomial_localized_special_fiber
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K)
    (Fs : List (MvPolynomial σ K[X]))
    (hrad : (Ideal.ofList (Fs.map (fun f =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p)
        (MvPolynomial.map (evalRingHom a) f)))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (Fs.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    let S := Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
    let t : S := algebraMap (MvPolynomial σ K[X]) S
      (MvPolynomial.C (σ := σ) (X - C a))
    RingTheory.Sequence.IsRegular (QuotSMulTop t S)
      (Fs.map (algebraMap (MvPolynomial σ K[X]) S)) := by
  let S := Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
  let : CommRing S := inferInstance
  let t : S := algebraMap (MvPolynomial σ K[X]) S
    (MvPolynomial.C (σ := σ) (X - C a))
  change RingTheory.Sequence.IsRegular (QuotSMulTop t S)
    (Fs.map (algebraMap (MvPolynomial σ K[X]) S))
  let e : (S ⧸ Ideal.span {t}) ≃ₐ[K] Localization.AtPrime p :=
    mvPolynomialLocalQuotientAlgEquiv p a
  apply (isRegular_quotSMulTop_iff (K := K) (S := S) (R := Localization.AtPrime p)
    t e (Fs.map (algebraMap (MvPolynomial σ K[X]) S))).mpr
  have hreg := WeightedTorusJets.isRegular_parameters_mvPolynomial_localization K σ p
    (Fs.map (fun f => algebraMap (MvPolynomial σ K) (Localization.AtPrime p)
      (MvPolynomial.map (evalRingHom a) f))) hrad (by simpa only [List.length_map] using hlen)
  simpa only [List.map_map, Function.comp_def, e, t, S,
    mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap] using hreg

end WeightedTorusJets.Deformation

namespace WeightedTorusJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

noncomputable def polynomialDeformation (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial σ (Polynomial R) :=
  MvPolynomial.C (1 - Polynomial.X) * MvPolynomial.map Polynomial.C (f i) +
    MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ d

theorem polynomialDeformation_at_zero (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (polynomialDeformation f d i) = f i := by
  have hcomp : (Polynomial.evalRingHom (0 : R)).comp Polynomial.C = RingHom.id R := by
    ext r
    simp
  simp [polynomialDeformation, MvPolynomial.map_map, hcomp, MvPolynomial.map_id]

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

theorem isRegular_source_polynomialDeformation_special_fiber
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : σ → MvPolynomial σ K) (d : ℕ) (is : List σ)
    (hrad : (Ideal.ofList (is.map (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (is.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (Polynomial.evalRingHom (0 : K))))
    let t : S := algebraMap (MvPolynomial σ (Polynomial K)) S
      (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))
    RingTheory.Sequence.IsRegular (QuotSMulTop t S)
      ((is.map (WeightedTorusJets.polynomialDeformation f d)).map
        (algebraMap (MvPolynomial σ (Polynomial K)) S)) := by
  exact isRegular_mvPolynomial_localized_special_fiber p 0
    (is.map (WeightedTorusJets.polynomialDeformation f d))
    (by simpa only [List.map_map, Function.comp_def,
      WeightedTorusJets.polynomialDeformation_at_zero] using hrad)
    (by simpa only [List.length_map] using hlen)



open RingTheory.Sequence
open scoped Pointwise

theorem parameter_regular_after_quotient
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (t : R) (fs : List R) (ht : IsSMulRegular M t)
    (hfs : RingTheory.Sequence.IsRegular (QuotSMulTop t M) fs) :
    IsSMulRegular (M ⧸ (Ideal.ofList fs • ⊤ : Submodule R M)) t := by
  have h : RingTheory.Sequence.IsRegular M (t :: fs) := IsRegular.cons ht hfs
  have hp : List.Perm (t :: fs) (fs ++ [t]) := by
    exact List.perm_append_comm (l₁ := [t]) (l₂ := fs)
  have h' := IsLocalRing.isRegular_of_perm h hp
  exact (isWeaklyRegular_singleton_iff _ _).mp
    ((isWeaklyRegular_append_iff M fs [t]).mp h'.toIsWeaklyRegular).2

theorem flat_of_regular_uniformizer
    {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M]
    (t : R) (ht : Irreducible t) (hreg : IsSMulRegular M t) : Module.Flat R M := by
  have : Module.IsTorsionFree R M := ⟨fun r hr => by
    obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr.ne_zero ht
    obtain ⟨u, hu⟩ := h.symm
    rw [← hu]
    exact (hreg.pow n).mul (u.isSMulRegular M)⟩
  infer_instance

theorem flat_quotient_of_regular_special_fiber
    {A S M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    [IsNoetherian S M] (t : A) (ht : Irreducible t) (fs : List S)
    (hreg : IsSMulRegular M (algebraMap A S t))
    (hfs : RingTheory.Sequence.IsRegular (QuotSMulTop (algebraMap A S t) M) fs) :
    Module.Flat A (M ⧸ (Ideal.ofList fs • ⊤ : Submodule S M)) := by
  apply flat_of_regular_uniformizer t ht
  exact (isSMulRegular_map (algebraMap A S) fun m => algebraMap_smul S t m).mp
    (parameter_regular_after_quotient (algebraMap A S t) fs hreg hfs)

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial

theorem dvr_polynomial_at_linear
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) :
    IsDiscreteValuationRing (Localization.AtPrime I) := by
  apply IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] (P := I)
  rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
  exact (irreducible_X_sub_C a).ne_zero

theorem irreducible_parameter_at_linear
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) :
    Irreducible (algebraMap K[X] (Localization.AtPrime I) (X - C a)) := by
  have : IsDiscreteValuationRing (Localization.AtPrime I) := dvr_polynomial_at_linear I a hI
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  calc
    Ideal.map (algebraMap K[X] (Localization.AtPrime I)) I =
        Ideal.map (algebraMap K[X] (Localization.AtPrime I)) (Ideal.span {X - C a}) :=
      congrArg (Ideal.map (algebraMap K[X] (Localization.AtPrime I))) hI
    _ = _ := by rw [Ideal.map_span]; simp

noncomputable def residueFieldAtLinearAlgEquiv
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) : I.ResidueField ≃ₐ[K] K := by
  have : I.IsMaximal := by
    rw [hI]
    exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
  exact (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (K[X] ⧸ I) I.ResidueField)
    I.bijective_algebraMap_quotient_residueField).symm.trans
      ((Ideal.quotientEquivAlgOfEq K hI).trans (quotientSpanXSubCAlgEquiv a))

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial

theorem specialFiber_prime_comap_C
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K) :
    (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))).comap MvPolynomial.C =
      Ideal.span {X - C a} := by
  ext f
  rw [← ker_evalRingHom a]
  change MvPolynomial.map (evalRingHom a) (MvPolynomial.C f) ∈ p ↔ f.eval a = 0
  rw [MvPolynomial.map_C, ← Ideal.Quotient.eq_zero_iff_mem]
  let g : K →+* MvPolynomial σ K ⧸ p := (Ideal.Quotient.mk p).comp MvPolynomial.C
  change g (f.eval a) = 0 ↔ f.eval a = 0
  exact map_eq_zero_iff g g.injective

@[instance_reducible] noncomputable def parameterLocalAlgebra
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    Algebra (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) :=
  (Localization.localRingHom I (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
    MvPolynomial.C (hI.trans (specialFiber_prime_comap_C p a).symm)).toAlgebra

theorem parameterLocalAlgebra_isScalarTower
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    let := parameterLocalAlgebra p I a hI
    IsScalarTower K[X] (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := by
  let := parameterLocalAlgebra p I a hI
  apply IsScalarTower.of_algebraMap_eq
  intro f
  change algebraMap K[X] _ f =
    Localization.localRingHom I _ MvPolynomial.C _ (algebraMap K[X] _ f)
  rw [Localization.localRingHom_to_map]
  rfl

theorem parameterLocalAlgebra_parameter
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    let := parameterLocalAlgebra p I a hI
    algebraMap (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (algebraMap K[X] (Localization.AtPrime I) (X - C a)) =
      algebraMap (MvPolynomial σ K[X]) _ (MvPolynomial.C (X - C a)) := by
  let := parameterLocalAlgebra p I a hI
  exact Localization.localRingHom_to_map I _ MvPolynomial.C _ (X - C a)

theorem parameterLocalAlgebra_groundFieldTower
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    letI := parameterLocalAlgebra p I a hI
    IsScalarTower K (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := by
  let := parameterLocalAlgebra p I a hI
  have := parameterLocalAlgebra_isScalarTower p I a hI
  exact IsScalarTower.to₁₃₄ K K[X] (Localization.AtPrime I) _

theorem localized_polynomial_parameter_ne_zero
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K) :
    algebraMap (MvPolynomial σ K[X])
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (MvPolynomial.C (X - C a)) ≠ 0 := by
  intro h
  have hC : MvPolynomial.C (σ := σ) (X - C a) = 0 :=
    (FaithfulSMul.algebraMap_injective (MvPolynomial σ K[X]) _)
      (h.trans (map_zero _).symm)
  exact X_sub_C_ne_zero a ((MvPolynomial.C_injective σ K[X])
    (hC.trans (map_zero _).symm))

theorem parameterLocalAlgebra_parameter_regular
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    letI := parameterLocalAlgebra p I a hI
    IsSMulRegular
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
      (algebraMap (Localization.AtPrime I)
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
          (algebraMap K[X] (Localization.AtPrime I) (X - C a))) := by
  let := parameterLocalAlgebra p I a hI
  rw [parameterLocalAlgebra_parameter]
  exact IsSMulRegular.of_ne_zero (localized_polynomial_parameter_ne_zero p a)

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

theorem flat_ideal_quotient_of_flat_smul_top
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (I : Ideal S)
    (hflat : Module.Flat A (S ⧸ (I • ⊤ : Submodule S S))) :
    Module.Flat A (S ⧸ I) := by
  let := hflat
  have hI : (I • ⊤ : Submodule S S) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact Module.Flat.of_linearEquiv
    (((Submodule.quotEquivOfEq _ _ hI).restrictScalars A).symm)

theorem ideal_ofList_ofFn_eq_span_range
    {S : Type*} [CommRing S] {n : ℕ} (f : Fin n → S) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  unfold Ideal.ofList
  congr 1
  ext x
  exact List.mem_ofFn' f x

theorem ideal_ofList_map_finRange_eq_span_range
    {S : Type*} [CommRing S] {n : ℕ} (f : Fin n → S) :
    Ideal.ofList ((List.finRange n).map f) = Ideal.span (Set.range f) := by
  rw [← List.ofFn_eq_map]
  exact ideal_ofList_ofFn_eq_span_range f

theorem flat_span_range_quotient_of_flat_ofFn_smul_top
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {n : ℕ} (f : Fin n → S)
    (hflat : Module.Flat A (S ⧸ (Ideal.ofList (List.ofFn f) • ⊤ : Submodule S S))) :
    Module.Flat A (S ⧸ Ideal.span (Set.range f)) := by
  let := flat_ideal_quotient_of_flat_smul_top (Ideal.ofList (List.ofFn f)) hflat
  exact Module.Flat.of_linearEquiv
    ((Ideal.quotientEquivAlgOfEq A (ideal_ofList_ofFn_eq_span_range f)).toLinearEquiv.symm)



open Polynomial
open scoped Pointwise

theorem flat_polynomialDeformation_localized
    {K : Type*} [Field K] {h : ℕ}
    (p : Ideal (MvPolynomial (Fin h) K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (hI : I = Ideal.span {X - C (0 : K)})
    (f : Fin h → MvPolynomial (Fin h) K) (d : ℕ)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (h : ℕ∞) = (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    letI := parameterLocalAlgebra p I 0 hI
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K))))
    letI : CommRing S := inferInstance
    Module.Flat (Localization.AtPrime I)
      (S ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)))) := by
  let := parameterLocalAlgebra p I 0 hI
  have := dvr_polynomial_at_linear I 0 hI
  let S := Localization.AtPrime
    (p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K))))
  let : CommRing S := inferInstance
  let fs : Fin h → S := fun i =>
    algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)
  apply flat_span_range_quotient_of_flat_ofFn_smul_top fs
  apply flat_quotient_of_regular_special_fiber
    (algebraMap K[X] (Localization.AtPrime I) (X - C (0 : K)))
    (irreducible_parameter_at_linear I 0 hI) (List.ofFn fs)
    (parameterLocalAlgebra_parameter_regular p I 0 hI)
  rw [show algebraMap (Localization.AtPrime I) S
      (algebraMap K[X] (Localization.AtPrime I) (X - C (0 : K))) =
      algebraMap (MvPolynomial (Fin h) K[X]) S (MvPolynomial.C (X - C (0 : K))) from
        parameterLocalAlgebra_parameter p I 0 hI]
  have hs := isRegular_source_polynomialDeformation_special_fiber p f d (List.finRange h)
    (by simpa only [ideal_ofList_map_finRange_eq_span_range] using hrad)
    (by simpa only [List.length_finRange] using hlen)
  simpa only [← List.ofFn_eq_map, List.map_ofFn, Function.comp_def] using hs

end WeightedTorusJets.Deformation



end SiegelZeros

end OAI
