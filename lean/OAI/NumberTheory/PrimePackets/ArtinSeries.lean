import Mathlib
import OAI.NumberTheory.PrimePackets.ArtinEuler
import OAI.NumberTheory.PrimePackets.FrobeniusConductor
import OAI.NumberTheory.PrimePackets.SplitEuler

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

def artinCoefficient (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ then
    if IsCoprime I (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) then
      (idealHom F E χ (integralIdealFractionalUnit I hI) : ℂ)
    else 0
  else 0

def artinDirichlet (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), artinCoefficient F E χ N I * (Ideal.absNorm I : ℂ)^(-s)

def badRationalPrimes (N : ℕ) : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime

namespace ArtinSeries
variable {F E} (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ)

abbrev allCoefficient := artinCoefficient F E χ N

@[simp] lemma allCoefficient_bot : allCoefficient χ N ⊥ = 0 := by
  simp [allCoefficient, artinCoefficient]
@[simp] lemma allCoefficient_zero : allCoefficient χ N 0 = 0 := allCoefficient_bot χ N
@[simp] lemma allCoefficient_one : allCoefficient χ N 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 F)) (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) :=
    by rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  have ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  simp only [Ideal.one_eq_top, allCoefficient, artinCoefficient, dite_eq_left ht, hc,
    ite_true, integralIdealFractionalUnit_top, map_one, Units.val_one]

lemma allCoefficient_mul (I J : Ideal (𝓞 F)) :
    allCoefficient χ N (I*J) = allCoefficient χ N I * allCoefficient χ N J := by
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  change I ≠ ⊥ at hI
  change J ≠ ⊥ at hJ
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [allCoefficient, artinCoefficient, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ,
    IsCoprime.mul_left_iff]
  by_cases hcI : IsCoprime I (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)
  · by_cases hcJ : IsCoprime J (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)
    · simp only [hcI, hcJ, and_self, ite_true]
      have H := congrArg (fun U : (FractionalIdeal (𝓞 F)⁰ F)ˣ =>
        (idealHom F E χ U : ℂ)) (EvenRayCharacter.integralUnit_mul I J hI hJ)
      simpa only [map_mul, Units.val_mul] using H
    · simp [hcI, hcJ]
  · simp [hcI]

def coefficientHom : Ideal (𝓞 F) →*₀ ℂ where
  toFun := allCoefficient χ N
  map_zero' := allCoefficient_zero χ N
  map_one' := allCoefficient_one χ N
  map_mul' := allCoefficient_mul χ N

lemma idealHom_norm (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : ‖(idealHom F E χ I : ℂ)‖ = 1 := by
  obtain ⟨e, he, hpow⟩ := idealHom_finiteOrder F E χ
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hpow I)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H

lemma allCoefficient_norm_le_one (I : Ideal (𝓞 F)) : ‖allCoefficient χ N I‖ ≤ 1 := by
  unfold allCoefficient artinCoefficient
  split_ifs with hI hc
  · rw [idealHom_norm χ]
  · simp
  · simp

def idealTerm {s : ℂ} (hs : 1 < s.re) : Ideal (𝓞 F) →*₀ ℂ :=
  coefficientHom χ N * (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)).comp Ideal.absNorm

lemma idealTerm_apply {s : ℂ} (hs : 1 < s.re) (I : Ideal (𝓞 F)) :
    idealTerm χ N hs I = allCoefficient χ N I * (Ideal.absNorm I : ℂ)^(-s) := rfl

 

lemma idealNorm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖(Ideal.absNorm I : ℂ)^(-s)‖) := by
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have hz : (0 : ℂ)^(-s) = 0 := Complex.zero_cpow (neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs))
  have hf (m : ℕ) :
      (∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m}, ‖(Ideal.absNorm I.val : ℂ)^(-s)‖) =
        ‖LSeries.term (fun k => (idealCoefficientReal F k : ℂ)) s m‖ := by
    simp only [show ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m},
      Ideal.absNorm I.val = m from fun I => I.property]
    by_cases hm : m = 0
    · subst m
      simp only [Nat.cast_zero, hz, norm_zero, tsum_zero, LSeries.term_zero]
    · rw [tsum_const, nsmul_eq_mul, LSeries.term_of_ne_zero hm, norm_div,
        idealCoefficientReal, ArithmeticFunction.coe_mk,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        idealCoefficient_pos F m hm, Complex.cpow_neg, norm_inv, div_eq_mul_inv]
  apply (summable_partition (fun I => norm_nonneg ((Ideal.absNorm I : ℂ)^(-s)))
    (s := fun m => {I : Ideal (𝓞 F) | Ideal.absNorm I = m})
    (fun I => ⟨Ideal.absNorm I, rfl, fun _ hx => hx.symm⟩)).mpr
  refine ⟨fun m => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 F) // Ideal.absNorm I = m} := Fintype.ofFinite _
    change Summable (fun I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m} =>
      ‖(Ideal.absNorm I.val : ℂ)^(-s)‖)
    exact (hasSum_fintype _).summable
  · change Summable (fun m : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m},
      ‖(Ideal.absNorm I.val : ℂ)^(-s)‖)
    simpa only [hf] using (idealCoefficient_LSeriesSummable F hs).norm

lemma idealTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (idealTerm χ N hs) := by
  apply Summable.of_norm_bounded (idealNorm_summable (F := F) hs)
  intro I
  rw [idealTerm_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (allCoefficient_norm_le_one χ N I)

def normTerm {s : ℂ} (hs : 1 < s.re) (m : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m}, idealTerm χ N hs I.val

lemma normTerm_zero {s : ℂ} (hs : 1 < s.re) : normTerm χ N hs 0 = 0 := by
  unfold normTerm
  have H : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 0}, idealTerm χ N hs I.val = 0 := by
    intro I
    rw [Ideal.absNorm_eq_zero_iff.mp I.property]
    exact map_zero _
  simp only [H, tsum_zero]

lemma normTerm_one {s : ℂ} (hs : 1 < s.re) : normTerm χ N hs 1 = 1 := by
  let oneI : {I : Ideal (𝓞 F) // Ideal.absNorm I = 1} := ⟨⊤, Ideal.absNorm_top⟩
  have h : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 1}, I = oneI := by
    intro I
    exact Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property)
  rw [normTerm, tsum_eq_single oneI (fun I hI => (hI (h I)).elim)]
  change idealTerm χ N hs (⊤ : Ideal (𝓞 F)) = 1
  rw [← Ideal.one_eq_top]
  exact map_one (idealTerm χ N hs)

lemma normTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (normTerm χ N hs) := by
  exact ((idealTerm_summable χ N hs).hasSum.tsum_fiberwise Ideal.absNorm).summable

lemma normTerm_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, normTerm χ N hs m) = artinDirichlet F E χ N s := by
  change (∑' m : ℕ, normTerm χ N hs m) = ∑' I : Ideal (𝓞 F), idealTerm χ N hs I
  exact ((idealTerm_summable χ N hs).hasSum.tsum_fiberwise Ideal.absNorm).tsum_eq

lemma normTerm_mul {s : ℂ} (hs : 1 < s.re) {m n : ℕ} (hc : m.Coprime n) :
    normTerm χ N hs (m*n) = normTerm χ N hs m * normTerm χ N hs n := by
  by_cases hm : m = 0
  · simp [hm, normTerm_zero χ N hs]
  by_cases hn : n = 0
  · simp [hn, normTerm_zero χ N hs]
  unfold normTerm
  rw [← (idealNormProductEquiv F m n hm hn hc).tsum_eq]
  change (∑' IJ : {I : Ideal (𝓞 F) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 F) // Ideal.absNorm J = n}, idealTerm χ N hs (IJ.1.val * IJ.2.val)) = _
  simp only [map_mul]
  exact (tsum_mul_tsum_of_summable_norm
    ((idealTerm_summable χ N hs).subtype _).norm
    ((idealTerm_summable χ N hs).subtype _).norm).symm

lemma prime_idealTerm_norm_lt_one {s : ℂ} (hs : 1 < s.re) {p : ℕ}
    (P : idealsOverPrime F p) : ‖idealTerm χ N hs P.val‖ < 1 := by
  have H := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le F P.property)
  change ‖allCoefficient χ N P.val *
    riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.val)‖ < 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (allCoefficient_norm_le_one χ N P.val)).trans_lt H

 

theorem primary_ideal_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    (∑' I : PrimaryIdeal F p, idealTerm χ N hs I.val) =
      ∏ P : idealsOverPrime F p, (1 - idealTerm χ N hs P.val)⁻¹ := by
  have HM (m : Multiset (idealsOverPrime F p)) :
      idealTerm χ N hs (primaryIdealMultisetEquiv F p m).val =
        (m.map (fun P => idealTerm χ N hs P.val)).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => exact map_one _
    | @cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
      exact congrArg (fun z => idealTerm χ N hs P.val * z) ih
  have HT := (complex_tsum_multiset_prod (fun P : idealsOverPrime F p =>
    idealTerm χ N hs P.val) (prime_idealTerm_norm_lt_one χ N hs)).2
  rw [← (primaryIdealMultisetEquiv F p).tsum_eq]
  exact (tsum_congr HM).trans HT

theorem local_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, normTerm χ N hs (p^e)) =
      ∏ P : idealsOverPrime F p, (1 - idealTerm χ N hs P.val)⁻¹ := by
  have HS : Summable (fun I : PrimaryIdeal F p => idealTerm χ N hs I.val) :=
    (idealTerm_summable χ N hs).subtype _
  have HE := (primaryIdealNormEquiv F p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σ e : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = p^e},
        idealTerm χ N hs I.2.val := HE.tsum_sigma.symm
    _ = ∑' I : PrimaryIdeal F p, idealTerm χ N hs I.val :=
      (primaryIdealNormEquiv F p hp).tsum_eq (fun I => idealTerm χ N hs I.val)
    _ = _ := primary_ideal_euler χ N hs

 
theorem dirichlet_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏ P : idealsOverPrime F (p:ℕ), (1 - idealTerm χ N hs P.val)⁻¹) (artinDirichlet F E χ N s) := by
  have HE := EulerProduct.eulerProduct_hasProd (normTerm_one χ N hs)
    (fun h => normTerm_mul χ N hs h) (normTerm_summable χ N hs).norm (normTerm_zero χ N hs)
  rw [normTerm_tsum χ N hs] at HE
  have he : (fun p : Nat.Primes => ∑' e : ℕ, normTerm χ N hs ((p:ℕ)^e)) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime F (p:ℕ),
        (1 - idealTerm χ N hs P.val)⁻¹) := by
    funext p
    exact local_euler χ N hs p.property
  rwa [he] at HE

end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
namespace ArtinSeries
lemma local_euler_bad (χ : (E ≃ₐ[F] E) →* ℂˣ) {N : ℕ}
    (p : Nat.Primes) (hpN : p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime F p.val, (1 - idealTerm χ N hs P.val)⁻¹) = 1 := by
  apply Finset.prod_eq_one
  intro P _
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hc : ¬ IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
    intro hc
    have hNm : (N : 𝓞 F) ∈ P.val := by
      obtain ⟨k, rfl⟩ := hpN
      rw [Nat.cast_mul]
      exact P.val.mul_mem_right _ hP.2
    have hle : ThetaConstruction.rationalModulusIdeal (𝓞 F) N ≤ P.val :=
      (Ideal.span_singleton_le_iff_mem _).mpr hNm
    apply hP.1.ne_top'
    apply eq_top_iff.mpr
    rw [← hc.codisjoint.eq_top]
    exact sup_le le_rfl hle
  have hz : artinCoefficient F E χ N P.val = 0 := by
    unfold artinCoefficient
    split
    · simp
    · rfl
  simp only [idealTerm_apply, allCoefficient, hz, zero_mul, sub_zero, inv_one]

variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _

lemma local_euler_good {N : ℕ} (hD : (NumberField.discr E).natAbs ∣ N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
      ∏ P : idealsOverPrime F p.val, (1 - idealTerm χ N hs P.val)⁻¹) =
        primeIdealEulerFactor E p.val s := by
  have hpC : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr hpN
  have hpD : p.val.Coprime (NumberField.discr E).natAbs :=
    hpC.of_dvd_right hD
  let (P : idealsOverPrime F p.val) : P.val.IsPrime :=
    ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
  let (P : idealsOverPrime F p.val) : Fintype (Ideal.primesOver P.val (𝓞 E)) :=
    (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  rw [Finset.prod_comm]
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F E p.val p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro P _
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hP0 : P.val ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hP
    exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)
  let PP : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P.val, hP.1, hP0⟩
  have hc : IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
    apply Ideal.isCoprime_iff_codisjoint.mpr
    apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
    exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpC.cast).codisjoint
  let Q := primeAbove F E PP
  let : Q.val.IsPrime := Q.property.1
  let : Algebra.IsUnramifiedAt (𝓞 F) (primeAbove F E PP).val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal Q.val Q.property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast hP.2)
  have he (χ : (E ≃ₐ[F] E) →* ℂˣ) :
      idealTerm χ N hs P.val =
        (χ (primeFrobenius F E PP) : ℂ) * (Ideal.absNorm P.val : ℂ)^(-s) := by
    rw [idealTerm_apply]
    change artinCoefficient F E χ N PP.asIdeal * _ = _
    have hc' : IsCoprime PP.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := hc
    rw [artinCoefficient, dite_eq_left PP.ne_bot, ite_eq_left hc', idealHom_prime]
  simp only [he]
  exact actual_cyclic_artin_localEuler F E PP s
end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance artinSeriesCharacterFintype : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _

 

theorem actual_cyclic_artin_factorization (N : ℕ) (hN : 0 < N)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s =
      (∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) *
        ∏ χ : (E ≃ₐ[F] E) →* ℂˣ, artinDirichlet F E χ N s := by
  let C : Nat.Primes → ℂ := fun p =>
    if p ∈ badRationalPrimes N then primeIdealEulerFactor E p.val s else 1
  have hC : HasProd C (∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) := by
    have h : HasProd C (∏ p ∈ badRationalPrimes N, C p) := hasProd_prod_of_ne_finset_one
      (s := badRationalPrimes N) (f := C) (fun p hp => ite_eq_right hp)
    simpa only [C, Finset.prod_ite_mem, Finset.inter_self] using h
  have hA := hasProd_prod (s := (Finset.univ : Finset ((E ≃ₐ[F] E) →* ℂˣ)))
    (fun χ _ => ArtinSeries.dirichlet_hasProd (F := F) (E := E) χ N hs)
  have hprod := hC.mul hA
  have he (p : Nat.Primes) :
      primeIdealEulerFactor E p.val s =
        C p * ∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
          ∏ P : idealsOverPrime F p.val, (1 - ArtinSeries.idealTerm χ N hs P.val)⁻¹ := by
    have hmem : p ∈ badRationalPrimes N ↔ p.val ∣ N := by
      change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
        N.primeFactors.subtype Nat.Prime ↔ p.val ∣ N
      rw [Finset.mem_subtype, Nat.mem_primeFactors]
      exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN.ne'⟩⟩
    by_cases hp : p.val ∣ N
    · simp only [C, ite_eq_left (hmem.mpr hp), ArtinSeries.local_euler_bad F E _ p hp hs,
        Finset.prod_const_one, mul_one]
    · dsimp only [C]
      rw [ite_eq_right (mt hmem.mp hp), one_mul]
      exact (ArtinSeries.local_euler_good F E hD p hp hs).symm
  exact (dedekindZeta_hasProd E hs).unique (hprod.congr_fun he)
end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
