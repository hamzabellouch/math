import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.FinrankDerivationCardTranscendenceBasis
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.NormalizationPresentationLocalEquiv

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.Geometry
open scoped BigOperators
variable (K ι : Type*) [CommRing K]
local notation "P" => MvPolynomial ι K
local notation "G" => ι →₀ ℤ
local notation "A" => AddMonoidAlgebra K G
local notation "L" => Localization.Away (∏ i : ι, (MvPolynomial.X i : P))

noncomputable def polynomialToLaurent : P →ₐ[K] A :=
  MvPolynomial.aeval fun i => AddMonoidAlgebra.single (Finsupp.single i 1) 1

@[simp] theorem polynomialToLaurent_X (i : ι) :
    polynomialToLaurent K ι (MvPolynomial.X i) =
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 :=
  MvPolynomial.aeval_X _ _

variable [Fintype ι]

noncomputable def localizationToLaurent : L →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (∏ i : ι, (MvPolynomial.X i : P))
    (f := polynomialToLaurent K ι) (by
    simpa [map_prod] using
      (Group.isUnit (Multiplicative.ofAdd (∑ i : ι, Finsupp.single i (1 : ℤ)))).map
        (AddMonoidAlgebra.of K G))

noncomputable def localizedCoordinateUnit (i : ι) : Lˣ :=
  (IsLocalization.Away.isUnit_of_dvd _
    (Finset.dvd_prod_of_mem (fun j : ι => (MvPolynomial.X j : P)) (Finset.mem_univ i))).unit

@[simp] theorem localizedCoordinateUnit_val (i : ι) :
    (localizedCoordinateUnit K ι i : L) = algebraMap P L (MvPolynomial.X i) := by
  rfl

noncomputable def localizedExponentHom : Multiplicative G →* Lˣ :=
  AddMonoidHom.toMultiplicativeLeft
    (Finsupp.liftAddHom fun i =>
      zmultiplesHom (Additive Lˣ) (Additive.ofMul (localizedCoordinateUnit K ι i)))

@[simp] theorem localizedExponentHom_single (i : ι) (n : ℤ) :
    localizedExponentHom K ι (Multiplicative.ofAdd (Finsupp.single i n)) =
      localizedCoordinateUnit K ι i ^ n := by
  simp [localizedExponentHom]

noncomputable def laurentToLocalization : A →ₐ[K] L :=
  AddMonoidAlgebra.lift K L G
    ((Units.coeHom L).comp (localizedExponentHom K ι))

noncomputable def laurentEquivLocalization : A ≃ₐ[K] L :=
  AlgEquiv.ofAlgHom (laurentToLocalization K ι) (localizationToLaurent K ι)
    (by
      ext i
      simp [Algebra.algHom, localizationToLaurent, laurentToLocalization])
    (by
      apply (AddMonoidAlgebra.lift K A G).symm.injective
      ext i
      simp [localizationToLaurent, laurentToLocalization])

@[simp] theorem laurentEquivLocalization_coordinate (i : ι) :
    laurentEquivLocalization K ι (AddMonoidAlgebra.single (Finsupp.single i 1) 1) =
      algebraMap P L (MvPolynomial.X i) := by
  simp [laurentEquivLocalization, laurentToLocalization]

end WeightedTorusJets.Geometry


section SamePrimeDimensionPrerequisites

namespace WeightedTorusJets.Geometry

theorem prime_height_eq_under_of_integral_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  have hf : StrictMono f := by
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  have hlift : ∀ a : PrimeSpectrum S, ∀ b : PrimeSpectrum R, b < f a →
      ∃ a' : PrimeSpectrum S, a' < a ∧ f a' = b := by
    intro a b hba
    obtain ⟨Q, hQa, hQ, hQb⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt a.asIdeal hba
    let := hQ
    let := hQb
    refine ⟨⟨Q, hQ⟩, hQa, ?_⟩
    apply PrimeSpectrum.ext
    exact (Q.over_def b.asIdeal).symm
  have h := Order.height_eq_of_strictMono f hf hlift
    (⟨P, inferInstance⟩ : PrimeSpectrum S)
  rw [← PrimeSpectrum.height_eq_orderHeight,
    ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h



theorem maximal_height_eq_ringKrullDim_of_finiteType
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (P : Ideal A) [P.IsMaximal] :
    (P.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : (P.under (MvPolynomial (Fin n) K)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  rw [prime_height_eq_under_of_integral_goingDown (R := MvPolynomial (Fin n) K) P,
    maximal_polynomial_height n (P.under (MvPolynomial (Fin n) K)),
    ringKrullDim_eq_of_integral_faithful_goingDown (R := MvPolynomial (Fin n) K)]
  simp




universe uK uA uF uC uE

theorem altitude_of_relative_fraction_fields
    {K : Type uK} {A : Type uA} {F : Type uF} {C : Type uC} {E : Type uE}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [Field F] [Algebra K F] [CommRing C] [IsDomain C] [Algebra F C]
    [Algebra.FiniteType F C] [Field E] [Algebra K E] [Algebra A E]
    [IsScalarTower K A E] [IsFractionRing A E] [Algebra F E] [Algebra C E]
    [IsScalarTower F C E] [IsFractionRing C E] [IsScalarTower K F E]
    (p : Ideal A) [p.IsPrime] (P : Ideal C) [P.IsMaximal]
    (hpht : p.height = P.height)
    (hF : Cardinal.lift.{uA} (Algebra.trdeg K F) =
      Cardinal.lift.{uF} (Algebra.trdeg K (A ⧸ p))) :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  obtain ⟨nA, hdimA, htrdegA⟩ := finiteType_dimension_trdeg (K := K) (A := A)
  obtain ⟨nC, hdimC, htrdegC⟩ := finiteType_dimension_trdeg (K := F) (A := C)
  obtain ⟨nQ, hdimQ, htrdegQ⟩ := finiteType_dimension_trdeg (K := K) (A := A ⧸ p)
  have hAE : Algebra.trdeg K E = nA := fractionField_trdeg_eq_nat nA htrdegA
  have hCE : Algebra.trdeg F E = nC := fractionField_trdeg_eq_nat nC htrdegC
  have hKF : Algebra.trdeg K F = nQ := by simpa [htrdegQ] using hF
  have htower := lift_trdeg_add_eq K F E
  have hsum : nQ + nC = nA := by
    simpa [hKF, hCE, hAE, ← Nat.cast_add] using htower
  rw [hpht, maximal_height_eq_ringKrullDim_of_finiteType (K := F), hdimC, hdimQ,
    hdimA, ← Nat.cast_add, Nat.add_comm nC nQ, hsum]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem exists_injective_polynomial_quotient_lift
    {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (p : Ideal A) (g : MvPolynomial ι K →ₐ[K] A ⧸ p)
    (hinj : Function.Injective g) :
    ∃ f : MvPolynomial ι K →ₐ[K] A,
      (Ideal.Quotient.mkₐ K p).comp f = g ∧ Function.Injective f := by
  classical
  choose x hx using fun i : ι => Ideal.Quotient.mkₐ_surjective K p (g (MvPolynomial.X i))
  let f : MvPolynomial ι K →ₐ[K] A := MvPolynomial.aeval x
  have hf : (Ideal.Quotient.mkₐ K p).comp f = g := by
    ext i
    simpa [f] using hx i
  refine ⟨f, hf, ?_⟩
  intro a b hab
  apply hinj
  simpa only [← hf, AlgHom.comp_apply] using congrArg (Ideal.Quotient.mkₐ K p) hab

theorem polynomial_quotient_lift_properties
    {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    (p : Ideal A) [p.IsPrime] (f : MvPolynomial ι K →ₐ[K] A)
    (g : MvPolynomial ι K →ₐ[K] A ⧸ p)
    (hf : (Ideal.Quotient.mkₐ K p).comp f = g)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    let : Algebra (MvPolynomial ι K) A := f.toRingHom.toAlgebra
    p.under (MvPolynomial ι K) = ⊥ ∧
      Algebra.IsIntegral (MvPolynomial ι K) (A ⧸ p) ∧
      Algebra.algebraMapSubmonoid A (nonZeroDivisors (MvPolynomial ι K)) ≤ p.primeCompl := by
  let : Algebra (MvPolynomial ι K) A := f.toRingHom.toAlgebra
  have hm : algebraMap (MvPolynomial ι K) (A ⧸ p) = g.toRingHom := by
    apply RingHom.ext
    intro b
    exact congrArg (fun h : MvPolynomial ι K →ₐ[K] A ⧸ p => h b) hf
  have hzero (b : MvPolynomial ι K) (hb : f b ∈ p) : b = 0 := by
    apply hinj
    rw [map_zero, ← hf, AlgHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · apply le_antisymm _ bot_le
    intro b hb
    exact Ideal.mem_bot.mpr (hzero b hb)
  · constructor
    intro b
    change (algebraMap (MvPolynomial ι K) (A ⧸ p)).IsIntegralElem b
    rw [hm]
    exact hint b
  · rintro b ⟨c, hc, rfl⟩
    change f c ∉ p
    intro hp
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hc) (hzero c hp)



theorem localized_prime_isMaximal_of_quotient_integral
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    (C : Type*) [CommRing C] [Algebra A C]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) C]
    (p : Ideal A) [p.IsPrime] (hp : p.under B = ⊥)
    [Algebra.IsIntegral B (A ⧸ p)] :
    (p.map (algebraMap A C)).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors B)
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    apply Set.disjoint_left.mpr
    rintro a ⟨b, hb, rfl⟩ ha
    have hbp : b ∈ p.under B := ha
    rw [hp] at hbp
    exact nonZeroDivisors.ne_zero hb hbp
  have : (p.map (algebraMap A C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M C p inferInstance hdisj
  let Q := C ⧸ p.map (algebraMap A C)
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ p) (nonZeroDivisors B)) Q := by
    simpa only [M, Algebra.algebraMapSubmonoid_map_map] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ p) M) Q)
  let f : FractionRing B →+* Q := IsLocalization.map Q (algebraMap B (A ⧸ p))
    (show nonZeroDivisors B ≤
      (Algebra.algebraMapSubmonoid (A ⧸ p) (nonZeroDivisors B)).comap _ from
        (nonZeroDivisors B).le_comap_map)
  let : Algebra (FractionRing B) Q := f.toAlgebra
  have : Algebra.IsIntegral (FractionRing B) Q :=
    ⟨isIntegral_localization (M := nonZeroDivisors B)⟩
  apply Ideal.Quotient.maximal_of_isField
  exact isField_of_isIntegral_of_isField' (R := FractionRing B) (S := Q) (Field.toIsField _)



variable {B A : Type*} [CommRing B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

theorem relative_denominators_le_nonZeroDivisors :
    Algebra.algebraMapSubmonoid A (nonZeroDivisors B) ≤ nonZeroDivisors A :=
  map_le_nonZeroDivisors_of_injective (algebraMap B A)
    (FaithfulSMul.algebraMap_injective B A) le_rfl

noncomputable abbrev relativeLocalizationFractionAlgebra :
    Algebra (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) (nonZeroDivisors A)
    relative_denominators_le_nonZeroDivisors

attribute [local instance] relativeLocalizationFractionAlgebra

theorem relativeLocalizationFraction_scalarTower :
    IsScalarTower A
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) (nonZeroDivisors A)
    relative_denominators_le_nonZeroDivisors

attribute [local instance] relativeLocalizationFraction_scalarTower

attribute [local instance] FractionRing.liftAlgebra

theorem relativeLocalization_fractionBase_scalarTower :
    IsScalarTower (FractionRing B)
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) := by
  let C := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B))
  have : IsScalarTower B C (FractionRing A) := IsScalarTower.to₁₃₄ B A C (FractionRing A)
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (nonZeroDivisors B)
  ext b
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem prime_height_add_quotient_dim_eq_of_finiteType
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : Ideal A) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ p)
  obtain ⟨f, hf, hfinj⟩ := exists_injective_polynomial_quotient_lift p g hginj
  let B := MvPolynomial (Fin n) K
  let : Algebra B A := f.toRingHom.toAlgebra
  let : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hfinj
  obtain ⟨hpB, hqint, hdenom⟩ := polynomial_quotient_lift_properties p f g hf hginj hgint
  let : Algebra.IsIntegral B (A ⧸ p) := hqint
  let : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors B)
  let C := Localization M
  let : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C
    (relative_denominators_le_nonZeroDivisors (B := B) (A := A))
  let : Algebra.FiniteType (FractionRing B) C := Algebra.FiniteType.equiv inferInstance
    (Localization.tensorRightAlgEquiv (nonZeroDivisors B) A)
  let P := p.map (algebraMap A C)
  let : P.IsMaximal := localized_prime_isMaximal_of_quotient_integral C p hpB
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    apply Set.disjoint_left.mpr
    intro a ha hpa
    exact hdenom ha hpa
  have hpht : p.height = P.height := by
    have hu : P.under A = p := IsLocalization.under_map_of_isPrime_disjoint M C
      inferInstance hdisj
    simpa only [hu] using IsLocalization.height_under M P
  let : Algebra C (FractionRing A) := relativeLocalizationFractionAlgebra
  let : IsScalarTower A C (FractionRing A) := relativeLocalizationFraction_scalarTower
  let : IsFractionRing C (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isLocalization M _ _
      (relative_denominators_le_nonZeroDivisors (B := B) (A := A))
  let : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B (FractionRing A)
  let : IsScalarTower (FractionRing B) C (FractionRing A) :=
    relativeLocalization_fractionBase_scalarTower
  have hqtr : Algebra.trdeg K (A ⧸ p) = n :=
    trdeg_eq_of_integral_polynomial_base n g hginj hgint
  have hftr : Algebra.trdeg K (FractionRing B) = n :=
    fractionField_trdeg_eq_nat (K := K) (A := B) (F := FractionRing B) n
      (by simp [B, MvPolynomial.trdeg_of_isDomain])
  apply altitude_of_relative_fraction_fields (K := K) (F := FractionRing B)
    (C := C) (E := FractionRing A) p P hpht
  simp [hftr, hqtr]



variable {K : Type*} [Field K]

theorem localization_mvPolynomial_ringKrullDim_le (n : ℕ)
    (M : Submonoid (MvPolynomial (Fin n) K))
    (S : Type*) [CommRing S] [Algebra (MvPolynomial (Fin n) K) S] [IsLocalization M S] :
    ringKrullDim S ≤ n := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro p hp
  have := hp
  rw [← IsLocalization.height_under M p]
  have h := (p.under (MvPolynomial (Fin n) K)).height_le_ringKrullDim_of_isPrime
  simpa using h

theorem torus_chart_ringKrullDim (n : ℕ) :
    ringKrullDim (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) = n := by
  let R := MvPolynomial (Fin n) K
  let t : R := ∏ i : Fin n, MvPolynomial.X i
  let T := Localization.Away t
  have hle : ringKrullDim T ≤ n :=
    localization_mvPolynomial_ringKrullDim_le n (Submonoid.powers t) T
  apply le_antisymm hle
  let p : Ideal R := RingHom.ker (MvPolynomial.eval (fun _ : Fin n ↦ (1 : K)))
  have hp : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (by
    intro c
    exact ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)
  have hdisj : Disjoint (Submonoid.powers t : Set R) (p : Set R) := by
    apply (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr
    change MvPolynomial.eval (fun _ : Fin n ↦ (1 : K))
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ≠ 0
    simp only [map_prod, MvPolynomial.eval_X, Finset.prod_const_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hpT : (p.map (algebraMap R T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) T p hp.isPrime hdisj
  have hheight : (p.map (algebraMap R T)).height = n := by
    rw [IsLocalization.height_map_of_disjoint (Submonoid.powers t) p hdisj]
    exact maximal_polynomial_height n p
  have h := (p.map (algebraMap R T)).height_le_ringKrullDim_of_isPrime
  simpa [hheight] using h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem torus_component_cotangent_eq_codimension {K : Type*} [Field K] (n : ℕ)
    (q : Ideal (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))) [q.IsPrime] :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) =
      n - ((ringKrullDim (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ q)).unbotD 0).toNat := by
  let R := MvPolynomial (Fin n) K
  let t : R := ∏ i : Fin n, MvPolynomial.X i
  let T := Localization.Away t
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    regular_localization_component (Submonoid.powers t) q
  have hheight : (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : WithBot ℕ∞) = q.height :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime q)).mp inferInstance).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q))
  have htotal := prime_height_add_quotient_dim_eq_of_finiteType (K := K) q
  rw [torus_chart_ringKrullDim, ← hheight] at htotal
  obtain ⟨d, hquot, _⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := T ⧸ q)
  change Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) =
    n - ((ringKrullDim (T ⧸ q)).unbotD 0).toNat
  have hsum : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) + d = n := by
    rw [show ringKrullDim (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ q) =
        (d : WithBot ℕ∞) from hquot] at htotal
    exact_mod_cast htotal
  simpa [hquot] using Nat.eq_sub_of_add_eq hsum

end WeightedTorusJets.Geometry

end SamePrimeDimensionPrerequisites


namespace WeightedTorusJets.Geometry

noncomputable def localizationResidueAlgEquiv {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    p.ResidueField ≃ₐ[R] IsLocalRing.ResidueField A :=
  IsLocalRing.ResidueField.mapAlgEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A)

theorem localization_residue_algEquiv_algebraMap {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] (x : R) :
    localizationResidueAlgEquiv (A := A) p (algebraMap R p.ResidueField x) =
      algebraMap R (IsLocalRing.ResidueField A) x :=
  (localizationResidueAlgEquiv (A := A) p).commutes x

theorem localization_residue_isFractionRing {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p]
    [Algebra (R ⧸ p) (IsLocalRing.ResidueField A)]
    [IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A)] :
    IsFractionRing (R ⧸ p) (IsLocalRing.ResidueField A) :=
  IsFractionRing.of_algEquiv
    ((localizationResidueAlgEquiv (A := A) p).extendScalarsOfSurjective
      (S := R ⧸ p) Ideal.Quotient.mk_surjective)

@[instance_reducible]
noncomputable def localizationResidueQuotientAlgebra {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
  ((localizationResidueAlgEquiv (A := A) p).toRingHom.comp
    (algebraMap (R ⧸ p) p.ResidueField)).toAlgebra

theorem localization_residue_quotientAlgebra_data {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
      localizationResidueQuotientAlgebra (A := A) p
    IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A) ∧
      IsFractionRing (R ⧸ p) (IsLocalRing.ResidueField A) := by
  let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
    localizationResidueQuotientAlgebra (A := A) p
  have h : IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (localization_residue_algEquiv_algebraMap (A := A) p x).symm
  exact ⟨h, localization_residue_isFractionRing p⟩

theorem localization_residue_quotientAlgebra_mk {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] (x : R) :
    let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
      localizationResidueQuotientAlgebra (A := A) p
    algebraMap (R ⧸ p) (IsLocalRing.ResidueField A) (Ideal.Quotient.mk p x) =
      algebraMap R (IsLocalRing.ResidueField A) x :=
  localization_residue_algEquiv_algebraMap (A := A) p x

end WeightedTorusJets.Geometry



end SiegelZeros

end OAI
