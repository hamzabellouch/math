import Mathlib
import OAI.NumberTheory.PrimePackets.MangoldtBounds
import OAI.NumberTheory.PrimePackets.PrimeFactors

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

lemma card_primeFactors_le_log {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have hpos : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  calc
    _ = ∑ _p ∈ q.primeFactors, Real.log 2 := by simp
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
      apply sum_le_sum
      intro p hp
      exact Real.log_le_log (by norm_num)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) :=
      (Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)).symm
    _ ≤ _ := by
      apply Real.log_le_log hpos
      have H := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
      simpa only [Nat.cast_prod] using (show (((∏ p ∈ q.primeFactors, p):ℕ):ℝ) ≤ (q:ℝ) by exact_mod_cast H)

variable (K : Type*) [Field K] [NumberField K]

lemma coprime_prime_sum_split (q N : ℕ) (hq : q ≠ 0) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
      (∑p ∈ q.primeFactors.filter (fun p => p ≤ N), idealCoefficientReal K p / p) =
    ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p := by
  have heq : q.primeFactors.filter (fun p => p ≤ N) =
      ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => p ∈ q.primeFactors) := by
    ext p
    simp only [mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp,hpN⟩
      exact ⟨⟨⟨(Nat.prime_of_mem_primeFactors hp).one_le,hpN⟩,
        Nat.prime_of_mem_primeFactors hp⟩,hp⟩
    · rintro ⟨⟨⟨_,hpN⟩,_⟩,hp⟩
      exact ⟨hp,hpN⟩
  rw [heq]
  rw [Finset.sum_filter (s := (Finset.Icc 1 N).filter Nat.Prime)
    (p := fun p => p ∈ q.primeFactors), ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hpP := (mem_filter.mp hp).2
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  by_cases hdiv : p ∣ q
  · have hps := Nat.mem_primeFactors.mpr ⟨hpP,hdiv,hq⟩
    have hnc : ¬p.Coprime q := by simpa only [hpP.coprime_iff_not_dvd,not_not] using hdiv
    simp [hps,hnc]
  · have hps : p ∉ q.primeFactors := by intro h; exact hdiv (Nat.dvd_of_mem_primeFactors h)
    have hcop : p.Coprime q := hpP.coprime_iff_not_dvd.mpr hdiv
    rw [ite_eq_left hcop]
    simp [hps]

lemma omitted_prime_tail (q : ℕ) {N : ℕ} (hN : 0 < N) :
    (∑p ∈ q.primeFactors.filter (fun p => N < p), idealCoefficientReal K p / p) ≤
      (Module.finrank ℤ (𝓞 K):ℝ) * q.primeFactors.card / N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑_p ∈ q.primeFactors.filter (fun p => N < p),
        (Module.finrank ℤ (𝓞 K):ℝ) / N := by
      apply sum_le_sum
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hpN : (N:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.le
      calc
        _ ≤ (Module.finrank ℤ (𝓞 K):ℝ) / p := by
          exact div_le_div_of_nonneg_right (idealCoefficientReal_prime_le K hpp) (Nat.cast_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hN0 hpN
    _ ≤ (q.primeFactors.card:ℝ) * ((Module.finrank ℤ (𝓞 K):ℝ)/N) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (by positivity)
    _ = _ := by ring

lemma prime_sum_add_log_bad_le {q N : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
      Real.log (badPrimeEuler K q) ≤
      (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) +
      (Module.finrank ℤ (𝓞 K):ℝ) * q.primeFactors.card / N +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  have hpartition : (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) =
      (∑p ∈ q.primeFactors.filter (fun p => p ≤ N), idealCoefficientReal K p / p) +
      (∑p ∈ q.primeFactors.filter (fun p => N < p), idealCoefficientReal K p / p) := by
    simpa only [not_le] using
      (sum_filter_add_sum_filter_not q.primeFactors (fun p => p ≤ N)
        (fun p => idealCoefficientReal K p / p)).symm
  have H := log_badPrimeEuler_le K q
  rw [hpartition] at H
  have HS := coprime_prime_sum_split K q N hq.ne'
  have HT := omitted_prime_tail K q (show 0 < N by omega)
  linarith

 

theorem coprime_prime_exponential_le_zeta {q N : ℕ} (hq : 0 < q) (hN : 2 ≤ N)
    (hqN : Real.log q ≤ N) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) ≤
      Real.exp (2*(Module.finrank ℤ (𝓞 K):ℝ) +
        (Module.finrank ℤ (𝓞 K):ℝ)/Real.log 2 +
        ((Module.finrank ℤ (𝓞 K):ℝ)^2 +
          localEulerTailConstant (Module.finrank ℤ (𝓞 K))) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
      (NumberField.dedekindZeta K (1+1/Real.log N)).re / badPrimeEuler K q := by
  let n : ℝ := Module.finrank ℤ (𝓞 K)
  let S : ℝ := ∑'m:ℕ, ((m:ℝ)^2)⁻¹
  let T := localEulerTailConstant (Module.finrank ℤ (𝓞 K))
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : (q.primeFactors.card:ℝ) ≤ N / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    exact (card_primeFactors_le_log hq).trans hqN
  have htail : n * q.primeFactors.card / N ≤ n / Real.log 2 := by
    calc
      _ ≤ n * ((N:ℝ)/Real.log 2) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hn) hN0.le
      _ = _ := by field_simp
  have H := prime_sum_add_log_bad_le K hq hN
  have He : Real.exp
      ((∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
        Real.log (badPrimeEuler K q)) ≤
      Real.exp ((∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) +
        n / Real.log 2 + T*S) := by
    apply Real.exp_le_exp.mpr
    dsimp only [n,S,T] at htail ⊢
    linarith
  rw [Real.exp_add,Real.exp_log (badPrimeEuler_pos K q)] at He
  apply (le_div_iff₀ (badPrimeEuler_pos K q)).mpr
  calc
    _ ≤ _ := He
    _ = Real.exp (n / Real.log 2 + T*S) *
        Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) := by
      simp only [Real.exp_add]
      
      ring
    _ ≤ Real.exp (n / Real.log 2 + T*S) * (Real.exp (2*n+n^2*S) *
        (NumberField.dedekindZeta K (1+1/Real.log N)).re) :=
      mul_le_mul_of_nonneg_left (ideal_prime_exponential_le_zeta K hN) (Real.exp_pos _).le
    _ = _ := by
      rw [←mul_assoc, ←Real.exp_add]
      congr 2
      dsimp [n,S,T]
      ring

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem coprime_ideal_relative_interval_normalized (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b : ℕ, 0 < q → Real.log q ≤ b →
          R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          (∑m ∈ Finset.Ioc a b, coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/Real.log b) *
              (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q := by
  obtain ⟨C,hC,hInt⟩ := Sieve.divisor_bounded_relative_interval n
  let E : ℝ := Real.exp (2*(n:ℝ)+(n:ℝ)/Real.log 2+
    ((n:ℝ)^2+localEulerTailConstant n)*∑'m:ℕ, ((m:ℝ)^2)⁻¹)
  refine ⟨C*E,mul_pos hC (Real.exp_pos _),?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt η hη
  refine ⟨max R 2,?_⟩
  intro K _ _ hn q a b hq hqb hb hab hrel
  have hb2 : 2 ≤ b := (le_max_right R 2).trans hb
  have hcoeff : ∀m, 0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤ (nFoldDivisor (n+1) m : ℝ) := by
    intro m
    simpa only [hn] using coprimeIdealCoefficient_bounds K q m
  have H := hR (coprimeIdealCoefficient K q)
    (coprimeIdealCoefficient_multiplicative K q) hcoeff a b
    ((le_max_left R 2).trans hb) hab hrel
  have hpe : Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) ≤
      E * (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q := by
    simpa only [E,hn,Sieve.smallPrimes] using coprime_prime_exponential_le_zeta K hq hb2 hqb
  have hfactor : 0 ≤ C * (((b:ℝ)-a)/Real.log b) := by
    apply mul_nonneg hC.le
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hab)
    · exact (Real.log_pos (by exact_mod_cast hb2 : (1:ℝ) < b)).le
  calc
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) := H
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        (E * (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q) :=
      mul_le_mul_of_nonneg_left hpe hfactor
    _ = _ := by ring

end PrimeDegreePackets


namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]

lemma idealsOverPrime_prime {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)

lemma idealsOverPrime_norm_power {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : ∃ e : ℕ, Ideal.absNorm P = p^e := by
  have HD : Ideal.absNorm P ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) :=
    map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))
  rw [Ideal.absNorm_span_natCast] at HD
  obtain ⟨e,-,he⟩ := (Nat.dvd_prime_pow hp).mp HD
  exact ⟨e,he⟩

 
def PrimaryIdeal (p : ℕ) :=
  {I : Ideal (𝓞 K) // I ≠ 0 ∧ ∀ P ∈ normalizedFactors I, P ∈ idealsOverPrime K p}

lemma primary_ideal_norm_power {p : ℕ} (hp : p.Prime) (I : PrimaryIdeal K p) :
    ∃ e : ℕ, Ideal.absNorm I.1 = p^e := by
  have HI := Ideal.prod_normalizedFactors_eq_self I.2.1
  rw [←HI, map_multiset_prod]
  have HA : ∀ m : Multiset (Ideal (𝓞 K)),
      (∀ P ∈ m, P ∈ idealsOverPrime K p) →
      ∃e : ℕ, (m.map Ideal.absNorm).prod = p^e := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0,by simp⟩
    | @cons P m ih =>
      intro hm
      obtain ⟨e,he⟩ := idealsOverPrime_norm_power K hp (hm P (by simp))
      obtain ⟨f,hf⟩ := ih (fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ))
      exact ⟨e+f,by simp [he,hf,pow_add]⟩
  exact HA _ I.2.2

 

def primaryIdealMultisetEquiv (p : ℕ) :
    Multiset (idealsOverPrime K p) ≃ PrimaryIdeal K p := by
  classical
  let F (m : Multiset (idealsOverPrime K p)) := (m.map Subtype.val).prod
  have hfac (m : Multiset (idealsOverPrime K p)) :
      normalizedFactors (F m) = m.map Subtype.val := by
    apply normalizedFactors_prod_of_prime
    intro P hP
    obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
    exact idealsOverPrime_prime K Q.2
  have hF (m : Multiset (idealsOverPrime K p)) : F m ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hP
    obtain ⟨Q,-,hQ⟩ := Multiset.mem_map.mp hP
    exact (idealsOverPrime_prime K Q.2).ne_zero hQ
  let f (m : Multiset (idealsOverPrime K p)) : PrimaryIdeal K p :=
    ⟨F m,hF m,by
      intro P hP
      rw [hfac] at hP
      obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro m l h
    have H := congrArg (fun I : PrimaryIdeal K p => normalizedFactors I.1) h
    change normalizedFactors (F m) = normalizedFactors (F l) at H
    rw [hfac,hfac] at H
    exact Multiset.map_injective Subtype.val_injective H
  · intro I
    let m : Multiset (idealsOverPrime K p) :=
      (normalizedFactors I.1).attach.map (fun P => ⟨P.1,I.2.2 P.1 P.2⟩)
    refine ⟨m,Subtype.ext ?_⟩
    change ((normalizedFactors I.1).attach.map _ |>.map Subtype.val).prod = I.1
    simp only [Multiset.map_map,Function.comp_def,Multiset.attach_map_val]
    exact Ideal.prod_normalizedFactors_eq_self I.2.1

 

def primaryIdealNormEquiv (p : ℕ) (hp : p.Prime) :
    (Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) ≃ PrimaryIdeal K p := by
  classical
  let f (a : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) : PrimaryIdeal K p :=
    ⟨a.2.1,by
      intro hz
      have H := a.2.2
      rw [hz,_root_.map_zero] at H
      exact (pow_ne_zero _ hp.ne_zero) H.symm,
      fun P hP => ideal_factor_mem_over K hp a.2.2 hP⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨e,I⟩ ⟨d,J⟩ he
    have hIJ : I.1 = J.1 := congrArg (fun I : PrimaryIdeal K p => I.1) he
    have hed : p^e = p^d := by rw [←I.2,←J.2,hIJ]
    have hed' := (Nat.pow_right_injective hp.two_le) hed
    subst d
    exact congrArg (Sigma.mk e) (Subtype.ext hIJ)
  · intro I
    obtain ⟨e,he⟩ := primary_ideal_norm_power K hp I
    exact ⟨⟨e,⟨I.1,he⟩⟩,Subtype.ext rfl⟩

end PrimeDegreePackets


namespace PrimeDegreePackets
open scoped ENNReal

 
lemma ennreal_tsum_multiset_prod {α : Type*} [Fintype α] (f : α → ℝ≥0∞) :
    (∑'m : Multiset α, (m.map f).prod) = ∏a, (1-f a)⁻¹ := by
  classical
  let e : (α → ℕ) ≃ Multiset α :=
    Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.symm.toEquiv
  have hm (m : Multiset α) : (m.map f).prod = ∏ a, f a ^ m.count a := by
    rw [prod_multiset_map_count]
    apply Finset.prod_subset (subset_univ _)
    intro a _ ha
    rw [Multiset.count_eq_zero.mpr (by simpa using ha),pow_zero]
  rw [←e.tsum_eq]
  simp only [hm]
  have he (k : α → ℕ) (a : α) : (e k).count a = k a := by
    simp [e]
  simp only [he]
  rw [ennreal_tsum_fintype_prod]
  simp only [ENNReal.tsum_geometric]

variable (K : Type*) [Field K] [NumberField K]

@[simp] lemma primaryIdealMultisetEquiv_val (p : ℕ) (m : Multiset (idealsOverPrime K p)) :
    (primaryIdealMultisetEquiv K p m).val = (m.map Subtype.val).prod := rfl

@[simp] lemma primaryIdealNormEquiv_val (p : ℕ) (hp : p.Prime)
    (I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) :
    (primaryIdealNormEquiv K p hp I).val = I.2.val := rfl

lemma primary_ideal_inverse_norm_series {p : ℕ} (hp : p.Prime) :
    (∑' I : PrimaryIdeal K p, ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹)) =
      ENNReal.ofReal (idealPrimeEuler K p) := by
  classical
  rw [←(primaryIdealNormEquiv K p hp).tsum_eq]
  simp only [primaryIdealNormEquiv_val]
  rw [ENNReal.tsum_sigma (fun e (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) =>
    ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹))]
  rw [idealPrimeEuler,ENNReal.ofReal_tsum_of_nonneg
    (fun _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
      (idealPrimeEuler_summable K hp)]
  apply tsum_congr
  intro e
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} := Fintype.ofFinite _
  have HE : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
    ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹)) =
      fun _ => ENNReal.ofReal (((p:ℝ)^e)⁻¹) := by
    funext I
    rw [I.2,Nat.cast_pow]
  rw [HE,tsum_fintype,sum_const]
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,
    idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero),Nat.card_eq_fintype_card]
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp.pos
  rw [ENNReal.ofReal_div_of_pos (pow_pos hpR e),
    ENNReal.ofReal_inv_of_pos (pow_pos hpR e)]
  simp only [nsmul_eq_mul,div_eq_mul_inv]
  simp

lemma idealsOverPrime_norm_two_le {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : 2 ≤ Ideal.absNorm P := by
  have hP0 : Ideal.absNorm P ≠ 0 := by
    exact fun he => (idealsOverPrime_prime K hP).ne_zero (Ideal.absNorm_eq_zero_iff.mp he)
  have hP1 : Ideal.absNorm P ≠ 1 := by
    intro he
    have := Ideal.absNorm_eq_one_iff.mp he
    exact (idealsOverPrime_prime K hP).not_isUnit (by simp [this])
  omega

 

theorem idealPrimeEuler_eq_primeIdeal_product {p : ℕ} (hp : p.Prime) :
    idealPrimeEuler K p = ∏P ∈ idealsOverPrime K p,
      (1 - (Ideal.absNorm P : ℝ)⁻¹)⁻¹ := by
  classical
  have HM (m : Multiset (idealsOverPrime K p)) :
      ENNReal.ofReal ((Ideal.absNorm (primaryIdealMultisetEquiv K p m).1 : ℝ)⁻¹) =
      (m.map (fun P => ENNReal.ofReal ((Ideal.absNorm P.1 : ℝ)⁻¹))).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, Nat.cast_mul,
        mul_inv_rev]
      rw [mul_comm, ENNReal.ofReal_mul (by positivity : 0 ≤ (Ideal.absNorm P.1 : ℝ)⁻¹)]
      simpa only [primaryIdealMultisetEquiv_val] using congrArg
        (fun x : ℝ≥0∞ => ENNReal.ofReal ((Ideal.absNorm P.1 : ℝ)⁻¹) * x) ih
  have H := primary_ideal_inverse_norm_series K hp
  rw [←(primaryIdealMultisetEquiv K p).tsum_eq] at H
  simp_rw [HM] at H
  rw [ennreal_tsum_multiset_prod] at H
  have HF (P : idealsOverPrime K p) :
      (1 - ENNReal.ofReal ((Ideal.absNorm P.1 : ℝ)⁻¹))⁻¹ =
      ENNReal.ofReal ((1 - (Ideal.absNorm P.1 : ℝ)⁻¹)⁻¹) := by
    have hn : (1:ℝ) < Ideal.absNorm P.1 := by
      exact_mod_cast idealsOverPrime_norm_two_le K P.2
    have hp' : 0 < (1:ℝ) - (Ideal.absNorm P.1 : ℝ)⁻¹ := by
      have := inv_lt_one_of_one_lt₀ hn
      linarith
    rw [ENNReal.ofReal_inv_of_pos hp', ENNReal.ofReal_sub 1 (by positivity),
      ENNReal.ofReal_one]
  simp_rw [HF] at H
  have HP : (∏ P : idealsOverPrime K p,
        ENNReal.ofReal ((1 - (Ideal.absNorm P.1 : ℝ)⁻¹)⁻¹)) =
      ENNReal.ofReal (∏ P : idealsOverPrime K p,
        (1 - (Ideal.absNorm P.1 : ℝ)⁻¹)⁻¹) := by
    symm
    apply ENNReal.ofReal_prod_of_nonneg
    intro P _
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    apply inv_le_one_of_one_le₀
    exact_mod_cast (idealsOverPrime_norm_two_le K P.2).trans' (by decide : 1 ≤ 2)
  rw [HP] at H
  have He := congrArg ENNReal.toReal H
  rw [ENNReal.toReal_ofReal (by
    apply Finset.prod_nonneg
    intro P _
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    apply inv_le_one_of_one_le₀
    exact_mod_cast (idealsOverPrime_norm_two_le K P.2).trans' (by decide : 1 ≤ 2)),
      ENNReal.toReal_ofReal (idealPrimeEuler_one_le K hp |>.trans' (by norm_num : (0:ℝ) ≤ 1))] at He
  have HH : (∏ P : idealsOverPrime K p, (1 - (Ideal.absNorm P.1 : ℝ)⁻¹)⁻¹) =
      ∏P ∈ idealsOverPrime K p, (1 - (Ideal.absNorm P : ℝ)⁻¹)⁻¹ :=
    Finset.prod_coe_sort (idealsOverPrime K p)
      (fun P : Ideal (𝓞 K) => (1 - (Ideal.absNorm P : ℝ)⁻¹)⁻¹)
  exact He.symm.trans HH

end PrimeDegreePackets
end
end

end OAI
