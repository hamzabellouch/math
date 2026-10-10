import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalFractionAlgebra

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
section
open TensorProduct
open TensorProduct
namespace WeightedTorusJets.Deformation

open TensorProduct

theorem exists_surjective_global_polynomial_quotient_to_local_generic_fiber
    {R A F S σ ι : Type*} [CommRing R] [CommRing A] [Field F] [CommRing S]
    [Algebra R A] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]
    (M : Submonoid R) [IsLocalization M A]
    (N : Submonoid (MvPolynomial σ R)) [IsLocalization N S]
    (f : ι → MvPolynomial σ R)
    [Module.Finite F (MvPolynomial σ F ⧸ Ideal.span
      (Set.range (fun i => MvPolynomial.map (algebraMap R F) (f i))))] :
    ∃ π : (MvPolynomial σ F ⧸ Ideal.span
        (Set.range (fun i => MvPolynomial.map (algebraMap R F) (f i)))) →ₗ[F]
        F ⊗[A] (S ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial σ R) S (f i)))),
      Function.Surjective π ∧ ∀ p : MvPolynomial σ R,
        π (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R F) p)) =
          1 ⊗ₜ[A] Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p) := by
  let I := Ideal.span (Set.range f)
  let E := mvPolynomialSpanQuotientBaseChange (A := F) f
  have : Module.Finite F (F ⊗[R] (MvPolynomial σ R ⧸ I)) :=
    Module.Finite.equiv E.symm.toLinearEquiv
  let qmap := Ideal.quotientMapₐ (I.map (algebraMap (MvPolynomial σ R) S))
    (IsScalarTower.toAlgHom R (MvPolynomial σ R) S) Ideal.le_comap_map
  let Tmap := Algebra.TensorProduct.map (AlgHom.id F F) qmap
  have hT : Function.Surjective Tmap :=
    surjective_baseChange_localized_quotient (R := R) (F := F)
      (P := MvPolynomial σ R) (S := S) N I
  let EB := genericFiberLocalBaseEquiv (A := A) (F := F)
    (B := S ⧸ I.map (algebraMap (MvPolynomial σ R) S)) M
  let EJ := Ideal.quotientEquivAlgOfEq A
    (show I.map (algebraMap (MvPolynomial σ R) S) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ R) S (f i))) by
        dsimp only [I]
        rw [Ideal.map_span, ← Set.range_comp'])
  let ET := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) EJ
  let π := ET.toLinearEquiv.toLinearMap.comp (EB.symm.toLinearEquiv.toLinearMap.comp
    (Tmap.toLinearMap.comp E.symm.toLinearEquiv.toLinearMap))
  refine ⟨π, ET.surjective.comp (EB.symm.surjective.comp (hT.comp E.symm.surjective)), ?_⟩
  intro p
  simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe,
    E, AlgEquiv.toLinearEquiv_apply,
    mvPolynomialSpanQuotientBaseChange_symm_mk_map]
  change ET (EB.symm (Tmap (1 ⊗ₜ[R] Ideal.Quotient.mk I p))) = _
  simp only [Tmap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    qmap]
  change ET (1 ⊗ₜ[A] Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p)) = _
  simp only [ET, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, EJ, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end WeightedTorusJets.Deformation

end


namespace WeightedTorusJets.Deformation

theorem finiteLength_quotient_of_radical_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hrad : I.radical = IsLocalRing.maximalIdeal R) :
    IsFiniteLength R (R ⧸ I) := by
  have hI : I ≠ ⊤ := by
    intro h
    have := congrArg (fun J : Ideal R => J.radical) h
    rw [hrad, Ideal.radical_top] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    apply IsLocalRing.eq_maximalIdeal
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using IsLocalRing.le_maximalIdeal hI)
  have hart : IsArtinianRing (R ⧸ I) := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ I)).mpr
    obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg (Ideal.fg_of_isNoetherianRing _)
    refine ⟨n, ?_⟩
    rw [← hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    rwa [hrad] at hn
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_quotient I,
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩

theorem finite_of_finiteLength_of_finite_residue
    {K R M : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    [Module.Finite K (IsLocalRing.ResidueField R)] (hM : IsFiniteLength R M) :
    Module.Finite K M := by
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R) ≠ ⊤ := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R)
      (IsLocalRing.residue_surjective (R := K))]
    exact Module.length_ne_top
  have hlen : Module.length K M ≠ ⊤ := by
    rw [IsLocalRing.length_restrictScalars K R M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) hres
  have : IsNoetherian K M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1
  infer_instance

theorem length_le_finrank_of_finiteLength_of_finite_residue
    {K R M : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    [Module.Finite K (IsLocalRing.ResidueField R)] (hM : IsFiniteLength R M) :
    Module.length R M ≤ (Module.finrank K M : ℕ∞) := by
  let := finite_of_finiteLength_of_finite_residue (K := K) hM
  have h := (⊤ : Submodule R M).length_le_length_restrictScalars K
  rw [Submodule.restrictScalars_top, Module.length_top, Module.length_top,
    Module.length_eq_finrank] at h
  exact h

theorem finite_quotient_of_radical_eq_maximalIdeal
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra K R] [Module.Finite K (IsLocalRing.ResidueField R)]
    (I : Ideal R) (hrad : I.radical = IsLocalRing.maximalIdeal R) :
    Module.Finite K (R ⧸ I) :=
  finite_of_finiteLength_of_finite_residue
    (finiteLength_quotient_of_radical_eq_maximalIdeal I hrad)

end WeightedTorusJets.Deformation

section

open TensorProduct

namespace WeightedTorusJets.Deformation

noncomputable def residueTensorQuotientAlgEquiv
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t}) :
    (IsLocalRing.ResidueField A ⊗[A] B) ≃ₐ[K]
      B ⧸ Ideal.span {algebraMap A B t} := by
  refine (((Algebra.TensorProduct.comm A (IsLocalRing.ResidueField A) B).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (IsLocalRing.maximalIdeal A)).symm.restrictScalars A)).restrictScalars K).trans ?_
  apply Ideal.quotientEquivAlgOfEq K
  rw [ht, Ideal.map_span]
  simp

theorem finite_residueTensor_of_finite_quotient
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t})
    [Module.Finite K (B ⧸ Ideal.span {algebraMap A B t})] :
    Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) := by
  have : Module.Finite K (IsLocalRing.ResidueField A ⊗[A] B) :=
    Module.Finite.of_surjective (residueTensorQuotientAlgEquiv (K := K) t ht).symm.toLinearMap
      (residueTensorQuotientAlgEquiv (K := K) t ht).symm.surjective
  exact Module.Finite.of_restrictScalars_finite K (IsLocalRing.ResidueField A) _

theorem finrank_residueTensor_eq_quotient
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t})
    (e : IsLocalRing.ResidueField A ≃ₐ[K] K) :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) =
      Module.finrank K (B ⧸ Ideal.span {algebraMap A B t}) := by
  have hdegree : Module.finrank K (IsLocalRing.ResidueField A) = 1 := by
    simpa using e.toLinearEquiv.finrank_eq
  have hdim := Module.finrank_mul_finrank K (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField A ⊗[A] B)
  rw [hdegree, one_mul] at hdim
  exact hdim.trans (residueTensorQuotientAlgEquiv (K := K) t ht).toLinearEquiv.finrank_eq

end WeightedTorusJets.Deformation

end

section

open Module TensorProduct

namespace WeightedTorusJets.Deformation

theorem finrank_special_fiber_le_generic
    (R F M : Type*) [CommRing R] [IsLocalRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)]
    [Module.Finite F (F ⊗[R] M)] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
      Module.finrank F (F ⊗[R] M) := by
  classical
  let k := IsLocalRing.ResidueField R
  let b := Module.finBasis k (k ⊗[R] M)
  choose v hv using fun i =>
    TensorProduct.mk_surjective R M k (IsLocalRing.residue_surjective (R := R)) (b i)
  have hspecial : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v) := by
    simpa only [Function.comp_def, hv] using b.linearIndependent
  have hbase : LinearIndependent R v := IsLocalRing.linearIndependent_of_flat v hspecial
  have hgeneric : LinearIndependent F (TensorProduct.mk R F M 1 ∘ v) :=
    hbase.of_isLocalizedModule F (nonZeroDivisors R) (TensorProduct.mk R F M 1)
  simpa using hgeneric.fintype_card_le_finrank

theorem finrank_special_fiber_le_global_generic
    (R F M G : Type*) [CommRing R] [IsLocalRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (π : G →ₗ[F] F ⊗[R] M) (hπ : Function.Surjective π) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
      Module.finrank F G := by
  have : Module.Finite F (F ⊗[R] M) := Module.Finite.of_surjective π hπ
  exact (finrank_special_fiber_le_generic R F M).trans
    (LinearMap.finrank_le_finrank_of_surjective hπ)

end WeightedTorusJets.Deformation

end


namespace WeightedTorusJets.Deformation

theorem finite_residueField_mvPolynomial_maximal
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsMaximal] : Module.Finite K p.ResidueField := by
  let := Ideal.Quotient.field p
  let : Module.Finite K (MvPolynomial σ K ⧸ p) :=
    finite_of_finite_type_of_isJacobsonRing K _
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p) p.ResidueField).toLinearMap
    p.bijective_algebraMap_quotient_residueField.surjective




open Polynomial

noncomputable def polynomialDeformationSpecialFiberAlgEquiv
    {K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : σ → MvPolynomial σ K) (d : ℕ) :
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (evalRingHom (0 : K))))
    letI : CommRing S := inferInstance
    let fs := fun i => algebraMap (MvPolynomial σ K[X]) S (polynomialDeformation f d i)
    let I := Ideal.span (Set.range fs)
    let t := algebraMap (MvPolynomial σ K[X]) S (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))
    ((S ⧸ I) ⧸ (Ideal.span {t}).map (Ideal.Quotient.mk I)) ≃ₐ[K]
      (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))) := by
  intro S
  letI : CommRing S := inferInstance
  have he := quotientFamilySpecializationAlgEquiv
    (Ideal.span {algebraMap (MvPolynomial σ K[X]) S
      (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))} : Ideal S)
    (mvPolynomialLocalQuotientAlgEquiv p (0 : K))
    (fun i => algebraMap (MvPolynomial σ K[X]) S (polynomialDeformation f d i))
    (fun i => algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))
    (fun i => by
      rw [mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap,
        polynomialDeformation_at_zero])
  exact he

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open Polynomial TensorProduct

theorem finrank_local_quotient_le_pow_of_radical
    {K : Type*} [Field K] (h d : ℕ)
    (p : Ideal (MvPolynomial (Fin h) K)) [p.IsMaximal]
    (f : Fin h → MvPolynomial (Fin h) K)
    (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.finrank K ((Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))) ≤ d ^ h := by
  let I : Ideal K[X] := RingHom.ker (evalRingHom (0 : K))
  have hI : I = Ideal.span {Polynomial.X - Polynomial.C (0 : K)} := ker_evalRingHom _
  let : I.IsPrime := RingHom.ker_isPrime (evalRingHom (0 : K))
  let A := Localization.AtPrime I
  let q := p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K)))
  let S := Localization.AtPrime q
  let : CommRing S := inferInstance
  let : Algebra A S := parameterLocalAlgebra p I (0 : K) hI
  have : IsScalarTower K[X] A S := parameterLocalAlgebra_isScalarTower p I (0 : K) hI
  have : IsScalarTower K A S := parameterLocalAlgebra_groundFieldTower p I (0 : K) hI
  have hFracTower := localFractionAlgebra_isScalarTower (F := RatFunc K) I
  have hFracField := localFractionAlgebra_isFractionRing (F := RatFunc K) I
  let : Algebra A (RatFunc K) := localFractionAlgebra (F := RatFunc K) I
  let : SMul A (RatFunc K) := (localFractionAlgebra (F := RatFunc K) I).toSMul
  have : IsScalarTower K[X] A (RatFunc K) := hFracTower
  have : IsFractionRing A (RatFunc K) := hFracField
  let Fs := fun i => algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)
  let J := Ideal.span (Set.range Fs)
  let B := S ⧸ J
  let t : A := algebraMap K[X] A (Polynomial.X - Polynomial.C (0 : K))
  let L := (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
    algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))
  have ht : IsLocalRing.maximalIdeal A = Ideal.span {t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    calc
      I.map (algebraMap K[X] A) =
          (Ideal.span {Polynomial.X - Polynomial.C (0 : K)}).map (algebraMap K[X] A) :=
        congrArg (Ideal.map (algebraMap K[X] A)) hI
      _ = _ := by
        rw [Ideal.map_span]
        simp only [Set.image_singleton]
        rfl
  let e : (B ⧸ Ideal.span {algebraMap A B t}) ≃ₐ[K] L := by
    have hJ : (Ideal.span {algebraMap A B t} : Ideal B) =
        (Ideal.span {algebraMap (MvPolynomial (Fin h) K[X]) S
          (MvPolynomial.C (σ := Fin h) (Polynomial.X - Polynomial.C (0 : K)))} : Ideal S).map
            (Ideal.Quotient.mk J) := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      congr 1
      rw [IsScalarTower.algebraMap_apply A S B, parameterLocalAlgebra_parameter]
      rfl
    exact (Ideal.quotientEquivAlgOfEq K hJ).trans
      (polynomialDeformationSpecialFiberAlgEquiv p f d)
  have : Module.Finite K p.ResidueField := finite_residueField_mvPolynomial_maximal p
  have : Module.Finite K L := finite_quotient_of_radical_eq_maximalIdeal _ hrad
  have : Module.Finite K (B ⧸ Ideal.span {algebraMap A B t}) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) :=
    finite_residueTensor_of_finite_quotient (K := K) t ht
  have hlen : (h : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height := by
    have hd := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      Geometry.maximal_polynomial_height h p] at hd
    exact_mod_cast hd.symm
  have : Module.Flat A B := flat_polynomialDeformation_localized p I hI f d hrad hlen
  let G := MvPolynomial (Fin h) (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
    MvPolynomial.map (algebraMap K[X] (RatFunc K)) (polynomialDeformation f d i)))
  obtain ⟨hfinite, hbound⟩ := generic_affine_deformation_quotient_bound f d hf
  let : Module.Finite (RatFunc K) G := hfinite
  obtain ⟨π, hπ, _⟩ := exists_surjective_global_polynomial_quotient_to_local_generic_fiber
    (A := A) (F := RatFunc K) (S := S) I.primeCompl q.primeCompl
      (polynomialDeformation f d)
  have hcomp := finrank_special_fiber_le_global_generic A (RatFunc K) B G π hπ
  rw [finrank_residueTensor_eq_quotient (K := K) t ht
    (residueFieldAtLinearAlgEquiv I (0 : K) hI), e.toLinearEquiv.finrank_eq] at hcomp
  exact hcomp.trans (by simpa only [Fintype.card_fin] using hbound)

theorem length_local_quotient_le_pow_of_radical
    {K : Type*} [Field K] (h d : ℕ)
    (p : Ideal (MvPolynomial (Fin h) K)) [p.IsMaximal]
    (f : Fin h → MvPolynomial (Fin h) K)
    (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p) ((Localization.AtPrime p) ⧸
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin h) K)
        (Localization.AtPrime p) (f i)))) ≤ (d ^ h : ℕ∞) := by
  have : Module.Finite K p.ResidueField := finite_residueField_mvPolynomial_maximal p
  exact (length_le_finrank_of_finiteLength_of_finite_residue (K := K)
    (finiteLength_quotient_of_radical_eq_maximalIdeal _ hrad)).trans
      (by exact_mod_cast finrank_local_quotient_le_pow_of_radical h d p f hf hrad)

end WeightedTorusJets.Deformation

end

end SiegelZeros

end OAI
