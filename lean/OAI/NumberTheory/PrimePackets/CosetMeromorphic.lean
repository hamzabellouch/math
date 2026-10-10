import Mathlib
import OAI.NumberTheory.PrimePackets.ArtinSeries
import OAI.NumberTheory.PrimePackets.PermutationArtin

namespace OAI

noncomputable section
open Module Filter Topology
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

 
def rationalPrimeSpectrum (p : Nat.Primes) (P : idealsOverPrime F p.val) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 F) := by
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  refine ⟨P.val, hP.1, ?_⟩
  intro he
  rw [he, Ideal.mem_bot] at hP
  exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)

 

def cosetRationalEuler (L : IntermediateField F E) (N : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if p.val ∣ N then 1 else
    ∏ P : idealsOverPrime F p.val,
      (LinearMap.det (LinearMap.id - (Ideal.absNorm P.val : ℂ)^(-s) •
        (LinearEquiv.funCongrLeft ℂ ℂ
          (MulAction.toPerm (β := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup)
            (primeFrobenius F E (rationalPrimeSpectrum F p P))⁻¹)).toLinearMap))⁻¹

lemma cosetRationalEuler_good (L : IntermediateField F E) {N : ℕ}
    (hD : (NumberField.discr E).natAbs ∣ N) (p : Nat.Primes) (hp : ¬ p.val ∣ N) (s : ℂ) :
    cosetRationalEuler F E L N p s = primeIdealEulerFactor L p.val s := by
  have hpD : p.val.Coprime (NumberField.discr E).natAbs :=
    (p.property.coprime_iff_not_dvd.mpr hp).of_dvd_right hD
  let (P : idealsOverPrime F p.val) : P.val.IsPrime :=
    ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
  let (P : idealsOverPrime F p.val) : Fintype (Ideal.primesOver P.val (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  rw [cosetRationalEuler, ite_eq_right hp]
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F L p.val p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro P _
  let PP := rationalPrimeSpectrum F p P
  let Q := primeAbove F E PP
  let : PP.asIdeal.IsMaximal := PP.isPrime.isMaximal PP.ne_bot
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E PP)
  let : Q.val.LiesOver PP.asIdeal := Q.property.2
  let : Algebra.IsUnramifiedAt (𝓞 F) Q.val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal Q.val Q.property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast
        ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).2)
  exact actual_nonnormal_artin_localEuler F E L PP.asIdeal PP.ne_bot Q.val
    (primeFrobenius F E PP) (primeFrobenius_spec F E PP) s

section EulerCorrection
variable (K : Type*) [Field K] [NumberField K]

 

def removedEulerPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ badRationalPrimes N, ∏ P : idealsOverPrime K p.val,
    (1 - (Ideal.absNorm P.val : ℂ)^(-s))

lemma primeEuler_denominator_ne_zero {p : ℕ} (P : idealsOverPrime K p)
    {s : ℂ} (hs : 0 < s.re) : 1 - (Ideal.absNorm P.val : ℂ)^(-s) ≠ 0 := by
  have hn : 1 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast (idealsOverPrime_norm_two_le K P.property)
  have hnorm : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
    rw [show (Ideal.absNorm P.val : ℂ) = ((Ideal.absNorm P.val : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hn (by simpa using neg_neg_of_pos hs)
  exact sub_ne_zero.mpr (fun h => by simp [← h] at hnorm)

lemma removedEulerPolynomial_entire (N : ℕ) :
    Differentiable ℂ (removedEulerPolynomial K N) := by
  apply Differentiable.fun_finsetProd
  intro p _
  apply Differentiable.fun_finsetProd
  intro P _
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (by have := idealsOverPrime_norm_two_le K P.property; omega :
      Ideal.absNorm P.val ≠ 0)
  exact (differentiable_const (1 : ℂ)).sub (differentiable_id.neg.const_cpow (Or.inl hn))

lemma removedEulerPolynomial_ne_zero (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    removedEulerPolynomial K N s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact primeEuler_denominator_ne_zero K P hs

end EulerCorrection

lemma cosetRationalEuler_hasProd (L : IntermediateField F E) (N : ℕ) (hN : 0 < N)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => cosetRationalEuler F E L N p s)
      (NumberField.dedekindZeta L s * removedEulerPolynomial L N s) := by
  let C : Nat.Primes → ℂ := fun p =>
    if p ∈ badRationalPrimes N then
      ∏ P : idealsOverPrime L p.val, (1 - (Ideal.absNorm P.val : ℂ)^(-s)) else 1
  have hC : HasProd C (removedEulerPolynomial L N s) := by
    have h : HasProd C (∏ p ∈ badRationalPrimes N, C p) := hasProd_prod_of_ne_finset_one (s := badRationalPrimes N) (f := C)
      (fun p hp => ite_eq_right hp)
    simpa only [C, Finset.prod_ite_mem, Finset.inter_self, removedEulerPolynomial] using h
  apply ((dedekindZeta_hasProd L hs).mul hC).congr_fun
  intro p
  have hpN : p ∈ badRationalPrimes N ↔ p.val ∣ N := by
    change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈ N.primeFactors.subtype Nat.Prime ↔ _
    rw [Finset.mem_subtype, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN.ne'⟩⟩
  by_cases hp : p.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hp, C, ite_eq_left (hpN.mpr hp)]
    unfold primeIdealEulerFactor
    rw [← Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (primeEuler_denominator_ne_zero L _ (zero_lt_one.trans hs)),
      Finset.prod_const_one]
  · simp only [C, ite_eq_right (mt hpN.mp hp), mul_one]
    exact cosetRationalEuler_good F E L hD p hp s

open HeckeMellin
section ContinuedCoset
variable {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

 

def cosetMeromorphic (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (N : ℕ) (s : ℂ) : ℂ :=
  removedEulerPolynomial K N s * (regularizedThetaZeta σ hn s / (s-1))

def cosetXiFactor (N : ℕ) (s : ℂ) : ℂ :=
  removedEulerPolynomial K N s *
    (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    ((Complex.Gamma (s/2))⁻¹)^(d+1) / s / (s-1)

lemma gammaInverse_entire :
    Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s/2))⁻¹) := by
  simpa only [one_div, Function.comp_def, id_eq] using
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2))

omit [NumberField.IsTotallyReal K] in
lemma exponentialInverse_entire : Differentiable ℂ
    (fun s : ℂ => (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹) := by
  have HE : Differentiable ℂ (completionExponential (d+1) |(NumberField.discr K : ℝ)|) :=
    fun s => (completionExponential_hasDerivAt _ _ s).differentiableAt
  exact HE.inv (fun s => completionExponential_ne_zero _ _ s)

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_meromorphicAt (N : ℕ) (s : ℂ) :
    MeromorphicAt (cosetXiFactor (K := K) (d := d) N) s := by
  have hA := (((removedEulerPolynomial_entire K N).analyticAt s).mul
    ((exponentialInverse_entire (K := K) (d := d)).analyticAt s)).mul
    ((gammaInverse_entire.analyticAt s).pow (d+1))
  exact (hA.meromorphicAt.div analyticAt_id.meromorphicAt).div
    (analyticAt_id.sub analyticAt_const).meromorphicAt

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_analyticAt (N : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (cosetXiFactor (K := K) (d := d) N) s := by
  have hA := (((removedEulerPolynomial_entire K N).analyticAt s).mul
    ((exponentialInverse_entire (K := K) (d := d)).analyticAt s)).mul
    ((gammaInverse_entire.analyticAt s).pow (d+1))
  exact (hA.div analyticAt_id hs0).div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hs1)

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_ne_zero (N : ℕ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    cosetXiFactor (K := K) (d := d) N s ≠ 0 := by
  apply div_ne_zero _ (sub_ne_zero.mpr hs1)
  apply div_ne_zero _ (by contrapose! hs; simp [hs])
  apply mul_ne_zero
  · exact mul_ne_zero (removedEulerPolynomial_ne_zero K N hs)
      (inv_ne_zero (completionExponential_ne_zero _ _ s))
  · exact pow_ne_zero _ (inv_ne_zero (Complex.Gamma_ne_zero (half_ne_nonpositive_integer hs)))

lemma cosetMeromorphic_eq_factor (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) :
    cosetMeromorphic σ hn N = cosetXiFactor (K := K) (d := d) N * completedThetaXi σ hn := by
  funext s
  simp only [cosetMeromorphic, cosetXiFactor, regularizedThetaZeta, Pi.mul_apply,
    div_eq_mul_inv]
  ring

lemma cosetMeromorphic_meromorphicAt (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) (s : ℂ) : MeromorphicAt (cosetMeromorphic σ hn N) s := by
  rw [cosetMeromorphic_eq_factor]
  exact (cosetXiFactor_meromorphicAt N s).mul
    ((completedThetaXi_entire σ hn).analyticAt s).meromorphicAt

lemma cosetMeromorphic_eq_dedekindZeta (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    cosetMeromorphic σ hn N s = NumberField.dedekindZeta K s * removedEulerPolynomial K N s := by
  have hs1 : s - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    simp [he] at hs
  rw [cosetMeromorphic, regularizedThetaZeta_eq_totallyReal σ hn hs,
    mul_div_cancel_left₀ _ hs1, mul_comm]

 

theorem cosetMeromorphic_order_eq (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
      meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ) := by
  have h0 : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0.ne'
  have h1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ1.ne
  rw [cosetMeromorphic_eq_factor]
  exact meromorphicOrderAt_mul_of_ne_zero (cosetXiFactor_analyticAt N h0 h1)
    (cosetXiFactor_ne_zero N hβ0 h1)

end ContinuedCoset

 

theorem actual_coset_meromorphic_pairing
    (L : IntermediateField F E) [NumberField.IsTotallyReal L] {d : ℕ}
    (σ : OrderedEmbeddings (d+1) L) (hn : finrank ℚ L = d+1)
    (N : ℕ) (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N) :
    (∀ s : ℂ, MeromorphicAt (cosetMeromorphic σ hn N) s) ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun p : Nat.Primes => cosetRationalEuler F E L N p s)
      (cosetMeromorphic σ hn N s)) ∧
    (∀ β : ℝ, 0 < β → β < 1 →
      meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
        meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ)) := by
  refine ⟨cosetMeromorphic_meromorphicAt σ hn N, ?_, ?_⟩
  · intro s hs
    rw [cosetMeromorphic_eq_dedekindZeta σ hn N hs]
    exact cosetRationalEuler_hasProd F E L N hN hD hs
  · intro β hβ0 hβ1
    exact cosetMeromorphic_order_eq σ hn N hβ0 hβ1

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
