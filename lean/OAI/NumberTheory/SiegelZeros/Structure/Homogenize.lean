import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.ConeMap

namespace OAI

namespace SiegelZeros




namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

local notation "𝒜" => MvPolynomial σ K
local notation "𝒮" => MvPolynomial (Option σ) K
local notation "𝒰" => Localization.Away (X (none : Option σ) : 𝒮)
local notation "𝒱" => Localization.Away (Polynomial.X : Polynomial 𝒜)

end WeightedTorusJets.Geometry



namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

noncomputable def homogenize (f : MvPolynomial σ K) : MvPolynomial (Option σ) K :=
  ∑ i ∈ Finset.range (f.totalDegree + 1),
    X none ^ (f.totalDegree - i) * rename some (homogeneousComponent i f)

theorem homogenize_isHomogeneous (f : MvPolynomial σ K) :
    (homogenize f).IsHomogeneous f.totalDegree := by
  apply IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hrename : (rename some (homogeneousComponent i f)).IsHomogeneous i := by
    rw [rename_eq_aeval]
    simpa only [one_mul] using (homogeneousComponent_isHomogeneous i f).aeval
      (X ∘ some) (fun j => isHomogeneous_X K (some j))
  simpa only [Nat.sub_add_cancel hi'] using
    (isHomogeneous_X_pow (R := K) (none : Option σ) (f.totalDegree - i)).mul hrename

theorem dehomogenize_homogenize (f : MvPolynomial σ K) :
    MvPolynomial.aeval (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X) (homogenize f) = f := by
  simp only [homogenize, map_sum, map_mul, map_pow, aeval_X, Option.elim_none,
    one_pow, one_mul, aeval_rename, Function.comp_def, Option.elim_some, aeval_X_left_apply]
  exact sum_homogeneousComponent f

theorem homogenize_totalDegree (f : MvPolynomial σ K) :
    (homogenize f).totalDegree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf, homogenize]
  · apply (homogenize_isHomogeneous f).totalDegree
    intro hzero
    apply hf
    rw [← dehomogenize_homogenize f, hzero, map_zero]

theorem map_span_homogenize (S : Set (MvPolynomial σ K)) :
    Ideal.map (MvPolynomial.aeval
      (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X)).toRingHom
      (Ideal.span (homogenize '' S)) = Ideal.span S := by
  rw [Ideal.map_span, Set.image_image]
  congr 1
  ext f
  simp only [Set.mem_image, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, dehomogenize_homogenize, exists_eq_right]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem span_homogenize_isHomogeneous (S : Set (MvPolynomial σ K)) :
    (Ideal.span (homogenize '' S)).IsHomogeneous
      (homogeneousSubmodule (Option σ) K) := by
  apply Ideal.homogeneous_span
  rintro f ⟨g, _, rfl⟩
  exact ⟨g.totalDegree, homogenize_isHomogeneous g⟩

theorem homogeneous_eval₂_mul
    {R S τ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial τ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (c : R →+* S) (x : τ → S) (t : S) :
    p.eval₂ c (fun i => x i * t) = p.eval₂ c x * t ^ n := by
  classical
  simp only [eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hn : n = ∑ i ∈ d.support, d i := hp.degree_eq_sum_deg_support hd
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hn, mul_assoc]

theorem eval₂_homogenize
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S) (t : S)
    (p : MvPolynomial σ K) :
    (homogenize p).eval₂ c (fun o : Option σ => o.elim t (fun i => x i * t)) =
      p.eval₂ c x * t ^ p.totalDegree := by
  have hx : (fun o : Option σ => o.elim t (fun i => x i * t)) =
      (fun o : Option σ => (o.elim 1 x) * t) := by
    funext o
    cases o <;> simp
  rw [hx, homogeneous_eval₂_mul (homogenize_isHomogeneous p)]
  congr 1
  have hcomp : (eval₂Hom c x).comp (MvPolynomial.aeval
      (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X)).toRingHom =
      eval₂Hom c (fun o : Option σ => o.elim 1 x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro o
      cases o <;> simp
  have h := congrArg (eval₂Hom c x) (dehomogenize_homogenize p)
  change ((eval₂Hom c x).comp (MvPolynomial.aeval
    (fun o : Option σ => o.elim (1 : MvPolynomial σ K) X)).toRingHom) (homogenize p) = _ at h
  rwa [hcomp] at h

theorem polynomial_eval₂_homogenize
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) :
    (homogenize p).eval₂ (Polynomial.C.comp c)
      (fun o : Option σ => o.elim Polynomial.X (fun i => Polynomial.C (x i) * Polynomial.X)) =
      Polynomial.C (p.eval₂ c x) * Polynomial.X ^ p.totalDegree := by
  rw [eval₂_homogenize, ← MvPolynomial.hom_eval₂]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem coneMap_homogenize (p : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    coneMap p (homogenize f) =
      Polynomial.C (Ideal.Quotient.mk p f) * Polynomial.X ^ f.totalDegree := by
  rw [coneMap, aeval_def]
  have halg : algebraMap K (Polynomial (MvPolynomial σ K ⧸ p)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K ⧸ p)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K ⧸ p) r
  rw [halg]
  rw [polynomial_eval₂_homogenize]
  congr 2
  have h : (MvPolynomial.aeval (fun i => Ideal.Quotient.mk p (X i)) :
      MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ p) = Ideal.Quotient.mkₐ K p := by
    ext i
    simp
  exact congrArg (fun g => g f) h

theorem homogenize_mem_coneIdeal (p : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} (hf : f ∈ p) : homogenize f ∈ coneIdeal p := by
  change coneMap p (homogenize f) = 0
  rw [coneMap_homogenize, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero, zero_mul]

theorem map_coneIdeal_dehomogenize (p : Ideal (MvPolynomial σ K)) :
    Ideal.map coneDehomogenize.toRingHom (coneIdeal p) = p := by
  apply le_antisymm (map_coneIdeal_dehomogenize_le p)
  intro f hf
  have hmem := Ideal.mem_map_of_mem coneDehomogenize.toRingHom
    (homogenize_mem_coneIdeal p hf)
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coneDehomogenize,
    dehomogenize_homogenize] using hmem

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem conePolynomialMap_homogenize {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) :
    conePolynomialMap (homogenize f) = Polynomial.C f * Polynomial.X ^ f.totalDegree := by
  rw [conePolynomialMap, aeval_def]
  have halg : algebraMap K (Polynomial (MvPolynomial σ K)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K) r
  rw [halg, polynomial_eval₂_homogenize, MvPolynomial.algebraMap_eq]
  simp

theorem conePolynomialMap_padded_homogenize {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (e : ℕ) :
    conePolynomialMap ((X (none : Option σ)) ^ e * homogenize f) =
      Polynomial.C f * Polynomial.X ^ (e + f.totalDegree) := by
  rw [map_mul, map_pow, conePolynomialMap_X_none, conePolynomialMap_homogenize, pow_add]
  exact mul_left_comm _ _ _

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem quotient_length_eq_of_flat_local_extension
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  let : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 3 1).mp hm.le
  have hlength : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    infer_instance
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange A B (A ⧸ I), hm, hlength, mul_one]

theorem quotient_length_local_polynomial
    {A : Type*} [CommRing A] [IsLocalRing A] (I : Ideal A) :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  dsimp only
  let : Module.Free A (Polynomial A) := .of_basis (Polynomial.basisMonomials A)
  apply quotient_length_eq_of_flat_local_extension
  rw [IsScalarTower.algebraMap_eq A (Polynomial A) _, ← Ideal.map_map,
    Polynomial.algebraMap_eq]
  exact Localization.AtPrime.map_eq_maximalIdeal

theorem local_polynomial_parameter_isUnit
    {A : Type*} [CommRing A] [IsLocalRing A] :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    IsUnit (algebraMap (Polynomial A) B Polynomial.X) := by
  dsimp only
  apply IsLocalization.map_units
    (M := ((IsLocalRing.maximalIdeal A).map
      (Polynomial.C : A →+* Polynomial A)).primeCompl) _ ⟨Polynomial.X, ?_⟩
  change Polynomial.X ∉
    (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
  intro h
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    simpa using (Ideal.mem_map_C_iff.mp h) 1
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    ((IsLocalRing.maximalIdeal A).eq_top_of_isUnit_mem h1 isUnit_one)



theorem span_range_mul_units {ι A : Type*} [CommRing A]
    (a u : ι → A) (hu : ∀ i, IsUnit (u i)) :
    Ideal.span (Set.range fun i => a i * u i) = Ideal.span (Set.range a) := by
  simp only [Ideal.span_range_eq_iSup, Ideal.span_singleton_mul_right_unit (hu _)]

theorem quotient_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) :
    Module.length B (B ⧸ I.map e) = Module.length A (A ⧸ I) := by
  rw [Module.length_quotient, Module.length_quotient]
  exact Order.coheight_orderIso e.idealComapOrderIso.symm I

theorem radical_map_eq_maximal_of_radical_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hm : (IsLocalRing.maximalIdeal A).map f = IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : I.radical = IsLocalRing.maximalIdeal A) :
    (I.map f).radical = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · exact (Ideal.radical_mono (Ideal.map_mono (I.le_radical.trans_eq hI))).trans_eq
      (by rw [hm]; exact Ideal.IsPrime.radical inferInstance)
  · rw [← hm, ← hI]
    exact Ideal.map_radical_le f

theorem mem_minimalPrimes_of_local_radical {A : Type*} [CommRing A]
    (p I : Ideal A) [p.IsPrime]
    (hI : (I.map (algebraMap A (Localization.AtPrime p))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    p ∈ I.minimalPrimes := by
  have hlocal : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      (I.map (algebraMap A (Localization.AtPrime p))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hI, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
    Set.mem_preimage, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p] at hlocal

theorem local_polynomial_scaled_span {ι A : Type*} [CommRing A] [IsLocalRing A]
    (a : ι → A) (e : ι → ℕ) :
    let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
    let B := Localization.AtPrime p
    Ideal.span (Set.range fun i =>
      algebraMap (Polynomial A) B (Polynomial.C (a i) * Polynomial.X ^ e i)) =
        (Ideal.span (Set.range a)).map (algebraMap A B) := by
  dsimp only
  let p := (IsLocalRing.maximalIdeal A).map (Polynomial.C : A →+* Polynomial A)
  let B := Localization.AtPrime p
  have hunit : IsUnit (algebraMap (Polynomial A) B Polynomial.X) :=
    local_polynomial_parameter_isUnit
  simp only [map_mul, map_pow]
  rw [span_range_mul_units _ _ (fun i => hunit.pow (e i)), Ideal.map_span, ← Set.range_comp]
  rfl



open MvPolynomial

noncomputable def paddedHomogenizedIdeal {ι K σ : Type*} [CommRing K]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) : Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span (Set.range fun i => (X (none : Option σ)) ^ n i * homogenize (f i))

theorem paddedHomogenizedIdeal_le_coneIdeal {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ∀ i, f i ∈ p) : paddedHomogenizedIdeal f n ≤ coneIdeal p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Ideal.mul_mem_left _ _ (homogenize_mem_coneIdeal p (hf i))

attribute [local instance] MvPolynomial.gradedAlgebra

theorem paddedHomogenizedIdeal_isHomogeneous {ι K σ : Type*} [CommRing K]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    (paddedHomogenizedIdeal f n).IsHomogeneous (homogeneousSubmodule (Option σ) K) := by
  apply Ideal.homogeneous_span (homogeneousSubmodule (Option σ) K)
  rintro _ ⟨i, rfl⟩
  exact ⟨n i + (f i).totalDegree,
    (isHomogeneous_X_pow (R := K) (none : Option σ) (n i)).mul (homogenize_isHomogeneous (f i))⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

attribute [local instance] coneIdeal_isPrime

theorem coneLocalEquiv_padded_ideal {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    let A := MvPolynomial σ K
    let R := Localization.AtPrime p
    let S := MvPolynomial (Option σ) K
    let L := Localization.AtPrime (coneIdeal p)
    let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
    ((paddedHomogenizedIdeal f n).map (algebraMap S L)).map (coneLocalEquiv p).toRingHom =
      ((Ideal.span (Set.range f)).map (algebraMap A R)).map (algebraMap R B) := by
  dsimp only
  let A := MvPolynomial σ K
  let R := Localization.AtPrime p
  let S := MvPolynomial (Option σ) K
  let L := Localization.AtPrime (coneIdeal p)
  let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
  have hgen (i : ι) : coneLocalEquiv p
      (algebraMap S L ((X (none : Option σ)) ^ n i * homogenize (f i))) =
      algebraMap (Polynomial R) B
        (Polynomial.C (algebraMap A R (f i)) * Polynomial.X ^ (n i + (f i).totalDegree)) := by
    rw [coneLocalEquiv_algebraMap, conePolynomialMap_padded_homogenize]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  calc
    _ = Ideal.span (Set.range fun i => algebraMap (Polynomial R) B
        (Polynomial.C (algebraMap A R (f i)) * Polynomial.X ^ (n i + (f i).totalDegree))) := by
      simp only [paddedHomogenizedIdeal, Ideal.map_span,
        ← Set.range_comp, Function.comp_def]
      exact congrArg (fun v : ι → B => Ideal.span (Set.range v)) (funext hgen)
    _ = (Ideal.span (Set.range fun i => algebraMap A R (f i))).map (algebraMap R B) :=
      local_polynomial_scaled_span (fun i => algebraMap A R (f i))
        (fun i => n i + (f i).totalDegree)
    _ = _ := by
      change (Ideal.span (Set.range fun i => algebraMap A R (f i))).map (algebraMap R B) =
        ((Ideal.span (Set.range f)).map (algebraMap A R)).map (algebraMap R B)
      congr 1
      rw [Ideal.map_span, ← Set.range_comp]
      rfl

theorem cone_padded_quotient_length {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    let A := MvPolynomial σ K
    let R := Localization.AtPrime p
    let S := MvPolynomial (Option σ) K
    let L := Localization.AtPrime (coneIdeal p)
    Module.length L (L ⧸ (paddedHomogenizedIdeal f n).map (algebraMap S L)) =
      Module.length R (R ⧸ (Ideal.span (Set.range f)).map (algebraMap A R)) := by
  dsimp only
  let : CommRing (Localization.AtPrime p) := inferInstance
  let : CommRing (Polynomial (Localization.AtPrime p)) := inferInstance
  let B := Localization.AtPrime
    ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C)
  refine (quotient_length_eq_of_ringEquiv (B := B)
    (coneLocalEquiv p).toRingEquiv _).symm.trans ?_
  exact (congrArg (fun I : Ideal B => Module.length B (B ⧸ I))
    (coneLocalEquiv_padded_ideal p f n)).trans (quotient_length_local_polynomial _)

theorem cone_padded_local_radical {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    ((paddedHomogenizedIdeal f n).map
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime (coneIdeal p)) := by
  let A := MvPolynomial σ K
  let R := Localization.AtPrime p
  let S := MvPolynomial (Option σ) K
  let L := Localization.AtPrime (coneIdeal p)
  let B := Localization.AtPrime ((IsLocalRing.maximalIdeal R).map Polynomial.C)
  let : CommRing R := inferInstance
  let : CommRing (Polynomial R) := inferInstance
  let J : Ideal L := (paddedHomogenizedIdeal f n).map (algebraMap S L)
  have hradB : (J.map (coneLocalEquiv p).toRingHom).radical = IsLocalRing.maximalIdeal B := by
    change (((paddedHomogenizedIdeal f n).map (algebraMap S L)).map
      (coneLocalEquiv p).toRingHom).radical = _
    rw [coneLocalEquiv_padded_ideal]
    apply radical_map_eq_maximal_of_radical_eq (A := R) (B := B) (algebraMap R B) _ _ hf
    rw [IsScalarTower.algebraMap_eq R (Polynomial R) _, ← Ideal.map_map,
      Polynomial.algebraMap_eq]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hradL : J.radical = IsLocalRing.maximalIdeal L := by
    let : IsLocalHom (coneLocalEquiv p).toRingHom :=
      IsLocalHom.of_surjective _ (coneLocalEquiv p).surjective
    have h := congrArg (Ideal.comap (coneLocalEquiv p).toRingHom) hradB
    rw [Ideal.comap_radical,
      Ideal.comap_map_of_bijective (coneLocalEquiv p).toRingHom (coneLocalEquiv p).bijective,
      IsLocalRing.maximalIdeal_comap] at h
    exact h
  exact hradL

theorem coneIdeal_mem_minimalPrimes_padded {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    coneIdeal p ∈ (paddedHomogenizedIdeal f n).minimalPrimes := by
  exact mem_minimalPrimes_of_local_radical (coneIdeal p) (paddedHomogenizedIdeal f n)
    (cone_padded_local_radical p f n hf)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem padded_homogenize_isHomogeneous_of_le {K σ : Type*} [CommSemiring K]
    (f : MvPolynomial σ K) (D : ℕ) (hf : f.totalDegree ≤ D) :
    ((X (none : Option σ)) ^ (D - f.totalDegree) * homogenize f).IsHomogeneous D := by
  simpa only [Nat.sub_add_cancel hf] using
    (isHomogeneous_X_pow (R := K) (none : Option σ) (D - f.totalDegree)).mul
      (homogenize_isHomogeneous f)

theorem padded_homogenize_totalDegree_le {K σ : Type*} [CommSemiring K]
    (f : MvPolynomial σ K) (D : ℕ) (hf : f.totalDegree ≤ D) :
    ((X (none : Option σ)) ^ (D - f.totalDegree) * homogenize f).totalDegree ≤ D :=
  (padded_homogenize_isHomogeneous_of_le f D hf).totalDegree_le

end WeightedTorusJets.Geometry




end SiegelZeros

end OAI
