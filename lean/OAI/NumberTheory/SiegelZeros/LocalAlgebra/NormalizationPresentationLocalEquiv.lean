import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.CoordinateLocalizedPrime
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueTensorQuotientAlgEquiv

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

noncomputable def normalizationPresentationLocalEquiv
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Localization.AtPrime P ≃ₐ[K]
      Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom) :=
  (Localization.localAlgEquiv (P.comap (normalizationPresentation e).symm.toRingHom) P
    (normalizationPresentation e).symm rfl).symm

theorem normalizationPresentationLocalEquiv_algebraMap
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (f : MvPolynomial σ K) :
    normalizationPresentationLocalEquiv e P (algebraMap _ (Localization.AtPrime P) f) =
      algebraMap _ (Localization.AtPrime
        (P.comap (normalizationPresentation e).symm.toRingHom))
          (normalizationPresentation e f) := by
  apply (normalizationPresentationLocalEquiv e P).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  change algebraMap _ (Localization.AtPrime P) f =
    Localization.localRingHom _ P (normalizationPresentation e).symm.toRingHom rfl
      (algebraMap _ _ (normalizationPresentation e f))
  rw [Localization.localRingHom_to_map]
  exact congrArg (algebraMap _ (Localization.AtPrime P))
    ((normalizationPresentation e).symm_apply_apply f).symm

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

theorem totalDegree_eval₂_le_of_linear_images
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : σ → MvPolynomial τ S)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (p.eval₂ (MvPolynomial.C.comp f) x).totalDegree ≤ p.totalDegree := by
  classical
  let φ := MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) x
  change (φ p).totalDegree ≤ p.totalDegree
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  calc
    _ ≤ (φ (MvPolynomial.C (p.coeff d))).totalDegree +
        (∑ i ∈ d.support, (φ (MvPolynomial.X i ^ d i)).totalDegree) :=
      (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add_left (MvPolynomial.totalDegree_finsetProd _ _) _)
    _ = ∑ i ∈ d.support, ((x i) ^ d i).totalDegree := by simp [φ]
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hx i))
    _ = d.sum (fun _ e => e) := rfl

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_localization_finrank_le_pow
    {B F : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (h D : ℕ) (p : Ideal (MvPolynomial (Fin h) B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial (Fin h) B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥)
    (f : Fin h → MvPolynomial (Fin h) B)
    (hf : ∀ i, (MvPolynomial.map (algebraMap B F) (f i)).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    let := coefficient_localization_isMaximal_of_finite (F := F) p hp
    let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
    Module.finrank F (Localization.AtPrime q ⧸ Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime q)
        (MvPolynomial.map (algebraMap B F) (f i))))) ≤ D ^ h := by
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
  let e := coefficientLocalizationLocalEquiv (F := F) p hp
  have hcomm (i : Fin h) : e (algebraMap _ (Localization.AtPrime p) (f i)) =
      algebraMap _ (Localization.AtPrime q)
        (MvPolynomial.map (algebraMap B F) (f i)) := by
    rw [AlgEquiv.commutes]
    rfl
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images
    e.toRingEquiv _ _ hcomm hrad
  exact WeightedTorusJets.Deformation.finrank_local_quotient_le_pow_of_radical h D q
    (fun i => MvPolynomial.map (algebraMap B F) (f i)) hf hrad'

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem totalDegree_normalizationPresentation_le
    {K σ ι τ : Type*} [Field K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (f : MvPolynomial σ K) :
    (normalizationPresentation e f).totalDegree ≤ (e.symm f).totalDegree := by
  let s := ((renameEquiv K (Equiv.sumComm ι τ)).trans (sumAlgEquiv K τ ι)).toRingHom
  have hs : s = eval₂Hom (C.comp (C : K →+* MvPolynomial ι K))
      (Sum.elim (fun i => C (X i)) X) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [s]
    · intro i
      cases i <;> simp [s]
  change (s (e.symm f)).totalDegree ≤ _
  rw [hs]
  apply totalDegree_eval₂_le_of_linear_images
  intro i
  cases i <;> simp

theorem totalDegree_localized_normalizationPresentation_le
    {K σ ι τ : Type*} [Field K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (f : MvPolynomial σ K) :
    (MvPolynomial.map (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)))
      (normalizationPresentation e f)).totalDegree ≤ (e.symm f).totalDegree := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans
    (totalDegree_normalizationPresentation_le e f)

theorem normalizationPresentation_radical_eq_maximal
    {K σ ι τ ν : Type*} [CommRing K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (f : ν → MvPolynomial σ K)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime P) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (Ideal.span (Set.range (fun i => algebraMap _
      (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom))
      (normalizationPresentation e (f i))))).radical = IsLocalRing.maximalIdeal
        (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom)) := by
  exact radical_span_eq_maximalIdeal_of_commuting_images
    (normalizationPresentationLocalEquiv e P).toRingEquiv
    (fun i => algebraMap _ (Localization.AtPrime P) (f i))
    (fun i => algebraMap _
      (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom))
      (normalizationPresentation e (f i)))
    (fun i => normalizationPresentationLocalEquiv_algebraMap e P (f i)) hrad

end WeightedTorusJets.Geometry.DegreeBezout

open Module TensorProduct

namespace WeightedTorusJets.Deformation

theorem finrank_eq_length_mul_residue_degree
    (K R M : Type*) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    [Module.Finite K M] [Module.Finite K (IsLocalRing.ResidueField R)] :
    (Module.finrank K M : ℕ∞) = Module.length R M *
      (Module.finrank K (IsLocalRing.ResidueField R) : ℕ∞) := by
  have h := IsLocalRing.length_restrictScalars K R M
  rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R)
    (IsLocalRing.residue_surjective (R := K)),
    Module.length_eq_finrank K M,
    Module.length_eq_finrank K (IsLocalRing.ResidueField R)] at h
  exact h

theorem finrank_localization_le (F A B : Type*) [Field F]
    [CommRing A] [Algebra F A] [Module.Finite F A]
    [CommRing B] [Algebra A B] [Algebra F B] [IsScalarTower F A B]
    (S : Submonoid A) [IsLocalization S B] :
    Module.finrank F B ≤ Module.finrank F A := by
  have : IsArtinianRing A := isArtinian_of_tower F (inferInstance : IsArtinian F A)
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (IsScalarTower.toAlgHom F A B).toLinearMap)
    (IsArtinianRing.localization_surjective S B)

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem component_local_artinian [IsNoetherianRing R] (hp : p ∈ I.minimalPrimes) :
    IsArtinianRing
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
    Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]

theorem component_local_length_ne_top [IsNoetherianRing R] (hp : p ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ := by
  have := component_local_artinian I p hp
  have : IsArtinian (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    isArtinian_of_surjective_algebraMap
      (R := Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      Ideal.Quotient.mk_surjective
  exact Module.length_ne_top

variable {K : Type*} [Field K]

theorem polynomial_component_regular (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := inferInstance

theorem regular_localization_component [IsRegularRing R]
    (M : Submonoid R) (q : Ideal (Localization M)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

theorem regular_localization_component_cotangent_dim [IsRegularRing R]
    (M : Submonoid R) (q : Ideal (Localization M)) [q.IsPrime] :
    (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : WithBot ℕ∞) =
        (q.comap (algebraMap R (Localization M))).height := by
  have := regular_localization_component M q
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height
    (q.comap (algebraMap R (Localization M))) (Localization.AtPrime q)]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance

theorem polynomial_component_height_bounds
    (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
    {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0) (hFp : F ∈ p) :
    1 ≤ p.height ∧ p.height ≤ 4 := by
  constructor
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hp
    apply hF
    simpa only [hp, Ideal.mem_bot] using hFp
  · have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    exact WithBot.coe_le_coe.mp (by simpa using h)

theorem polynomial_component_cotangent_dim
    (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime] :
    (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) : WithBot ℕ∞) = p.height := by
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance

theorem localization_component_cotangent_bounds
    (M : Submonoid (MvPolynomial (Fin 4) K))
    (p : Ideal (Localization M)) [p.IsPrime]
    {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0)
    (hFp : algebraMap (MvPolynomial (Fin 4) K) (Localization M) F ∈ p) :
    1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) ∧
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) ≤ 4 := by
  have hb := polynomial_component_height_bounds
    (p.comap (algebraMap (MvPolynomial (Fin 4) K) (Localization M))) hF hFp
  have hd := regular_localization_component_cotangent_dim M p
  have hd' := WithBot.coe_injective hd
  rw [← hd'] at hb
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

theorem map_extended_ideal_eq {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal R) :
    (I.map (algebraMap R A)).map e.toRingEquiv.toRingHom = I.map (algebraMap R B) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext e.commutes

noncomputable def quotientExtendedAlgEquiv {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal R) :
    (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B)) :=
  Ideal.quotientEquivAlg _ _ e (map_extended_ideal_eq e I).symm

theorem extended_quotient_length_eq {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal R) :
    Module.length A (A ⧸ I.map (algebraMap R A)) =
      Module.length B (B ⧸ I.map (algebraMap R B)) :=
  quotient_length_eq_of_ringEquiv e.toRingEquiv _ _ (map_extended_ideal_eq e I).symm

theorem local_quotient_length_eq_after_localization {R : Type*} [CommRing R]
    (S : Submonoid R) (p : Ideal (Localization S)) [p.IsPrime] (I : Ideal R) :
    Module.length (Localization.AtPrime (p.comap (algebraMap R (Localization S))))
      (Localization.AtPrime (p.comap (algebraMap R (Localization S))) ⧸
        I.map (algebraMap R (Localization.AtPrime
          (p.comap (algebraMap R (Localization S)))))) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
  extended_quotient_length_eq
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization S p) I



open IsLocalRing Module

section Local

variable (K R M : Type*) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

theorem field_length_eq_local_length_mul_residue_length :
    length K M = length R M * length K (ResidueField R) := by
  rw [IsLocalRing.length_restrictScalars K R M,
    ← Module.length_eq_of_surjective (M := ResidueField R)
      (IsLocalRing.residue_surjective (R := K))]

theorem finite_of_finite_length_of_finite_residue
    [Module.Finite K (ResidueField R)] (hM : IsFiniteLength R M) :
    Module.Finite K M := by
  have hlen : length K M ≠ ⊤ := by
    rw [field_length_eq_local_length_mul_residue_length K R M,
      Module.length_eq_finrank K (ResidueField R)]
    lift length R M to ℕ using Module.length_ne_top_iff.mpr hM with n hn
    rw [← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hfinite := Module.length_ne_top_iff.mp hlen
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  infer_instance

theorem finrank_eq_local_length_toNat_mul_residue_degree
    [Module.Finite K M] [Module.Finite K (ResidueField R)] :
    finrank K M = (length R M).toNat * finrank K (ResidueField R) := by
  simpa using congrArg ENat.toNat (WeightedTorusJets.Deformation.finrank_eq_length_mul_residue_degree K R M)

end Local


variable (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

theorem local_weighted_length_le_finrank (p : PrimeSpectrum A) :
    length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) *
      (finrank K (ResidueField (Localization.AtPrime p.asIdeal)) : ℕ∞) ≤
        finrank K A := by
  let R := Localization.AtPrime p.asIdeal
  let : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  have hsurj : Function.Surjective (algebraMap A R) :=
    IsArtinianRing.localization_surjective p.asIdeal.primeCompl R
  let : Module.Finite K R := Module.Finite.of_surjective
    (Algebra.algHom K A R).toLinearMap hsurj
  rw [← WeightedTorusJets.Deformation.finrank_eq_length_mul_residue_degree K R R,
    ← Module.length_eq_finrank K R, ← Module.length_eq_finrank K A]
  exact Module.length_le_of_surjective (Algebra.algHom K A R).toLinearMap hsurj

theorem finrank_eq_sum_local_length_mul_residue_degree
    [Fintype (PrimeSpectrum A)] :
    finrank K A = ∑ p : PrimeSpectrum A,
      (length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
        finrank K (ResidueField (Localization.AtPrime p.asIdeal)) := by
  let : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum A K]
  apply Finset.sum_congr rfl
  intro p _
  let R := Localization.AtPrime p.asIdeal
  let : Module.Finite K R := Module.Finite.of_surjective
    (Algebra.algHom K A R).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl R)
  exact finrank_eq_local_length_toNat_mul_residue_degree K R R


end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open IsLocalRing Module

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

theorem finite_residue_of_maximal [Algebra.FiniteType K A]
    (p : Ideal A) [p.IsMaximal] :
    Module.Finite K (ResidueField (Localization.AtPrime p)) := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Module.Finite K (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ p)
  let : Module.Finite (A ⧸ p) p.ResidueField := Module.Finite.of_surjective
    (Algebra.linearMap (A ⧸ p) p.ResidueField)
    p.bijective_algebraMap_quotient_residueField.surjective
  exact Module.Finite.trans (A ⧸ p) p.ResidueField

theorem isolated_quotient_finite [IsNoetherianRing A] [Algebra.FiniteType K A]
    (I p : Ideal A) [p.IsMaximal] (hp : p ∈ I.minimalPrimes) :
    Module.Finite K
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) := by
  let := finite_residue_of_maximal K A p
  exact finite_of_finite_length_of_finite_residue K (Localization.AtPrime p) _
    (Module.length_ne_top_iff.mp (component_local_length_ne_top I p hp))

theorem isolated_component_finrank [IsNoetherianRing A] [Algebra.FiniteType K A]
    (I p : Ideal A) [p.IsMaximal] (hp : p ∈ I.minimalPrimes) :
    (finrank K
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) : ℕ∞) =
      length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) *
          (finrank K (ResidueField (Localization.AtPrime p)) : ℕ∞) := by
  let := finite_residue_of_maximal K A p
  let := isolated_quotient_finite K A I p hp
  exact WeightedTorusJets.Deformation.finrank_eq_length_mul_residue_degree K
    (Localization.AtPrime p) _

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coefficientLocalizationResidueAlgEquiv
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    [Algebra F p.ResidueField] [IsScalarTower B F p.ResidueField]
    (hp : p.comap MvPolynomial.C = ⊥) :
    p.ResidueField ≃ₐ[F]
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField :=
  (IsLocalRing.ResidueField.mapAlgEquiv
    ((coefficientLocalizationLocalEquiv p hp).restrictScalars B)).extendScalarsOfIsLocalization
      F (nonZeroDivisors B)

theorem coefficient_localization_residue_degree_eq_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    [Algebra F p.ResidueField] [IsScalarTower B F p.ResidueField]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Module.finrank F
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField =
      Module.finrank B (MvPolynomial σ B ⧸ p) := by
  rw [← (coefficientLocalizationResidueAlgEquiv p hp).toLinearEquiv.finrank_eq]
  exact IsFractionRing.finrank_eq B F (MvPolynomial σ B ⧸ p) p.ResidueField

theorem projected_residue_degree_eq_component_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Module.finrank F
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField =
      Module.finrank B (MvPolynomial σ B ⧸ p) := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  exact coefficient_localization_residue_degree_eq_rank p hp

theorem coefficient_localization_quotient_length
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) =
    Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) := by
  dsimp only
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact extended_quotient_length_eq (coefficientLocalizationLocalEquiv p hp) I

theorem coefficient_localization_component_finrank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank F (IsLocalRing.ResidueField (Localization.AtPrime q)) : ℕ∞) := by
  let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
  let M : Submonoid (MvPolynomial σ B) := (nonZeroDivisors B).map MvPolynomial.C
  have hq : q ∈ (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map M (MvPolynomial σ F) I, Set.mem_preimage]
    change q.comap (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) ∈ I.minimalPrimes
    have he := IsLocalization.under_map_of_isPrime_disjoint M (MvPolynomial σ F)
      (show p.IsPrime from inferInstance) (coefficient_nonZeroDivisors_disjoint p hp)
    change q.comap (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p at he
    rwa [he]
  have h := isolated_component_finrank F (MvPolynomial σ F)
    (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))) q hq
  rw [← coefficient_localization_quotient_length I p hp] at h
  exact h

theorem coefficient_localization_component_finrank_eq_length_mul_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank B (MvPolynomial σ B ⧸ p) : ℕ∞) := by
  rw [← projected_residue_degree_eq_component_rank (F := F) p hp]
  exact coefficient_localization_component_finrank I p hp hpI

end WeightedTorusJets.Geometry.DegreeBezout

end

end SiegelZeros

end OAI
