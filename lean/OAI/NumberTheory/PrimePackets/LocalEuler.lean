import Mathlib
import OAI.NumberTheory.PrimePackets.IdealSupport
import OAI.NumberTheory.PrimePackets.PrimeSums

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
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors

 

def primaryIdealSingletonEquiv (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) : primaryIntegralIdeals K {p} ≃ PrimaryIdeal K p where
  toFun J := ⟨J.1.1,J.1.2,by
    have hk := Nat.eq_prime_pow_of_unique_prime_dvd
      (Ideal.absNorm_eq_zero_iff.not.mpr J.1.2) (fun {r} hr hd => by simpa using J.2 r hr hd)
    exact fun P hP => ideal_factor_mem_over K hp hk hP⟩
  invFun I := ⟨⟨I.1,I.2.1⟩,by
    intro r hr hd
    obtain ⟨k,hk⟩ := primary_ideal_norm_power K hp I
    rw [hk] at hd
    have he := (Nat.dvd_prime hp).mp (hr.dvd_of_dvd_pow hd)
    simpa using he.resolve_left hr.ne_one⟩
  left_inv _ := rfl
  right_inv _ := rfl

 

theorem actual_localZ_eq_idealPrimeEuler (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    (localZinv (actualLocalModel p K).Ring)⁻¹ = ENNReal.ofReal (idealPrimeEuler K p) := by
  classical
  let S : Finset ℕ := {p}
  let : ∀ r : S, Fact r.val.Prime := fun r => ⟨by
    have hr : r.val = p := Finset.mem_singleton.mp r.2
    simpa [hr] using (Fact.out : p.Prime)⟩
  let : Unique S := ⟨⟨⟨p,by simp [S]⟩⟩,fun r => Subtype.ext (Finset.mem_singleton.mp r.2)⟩
  have h := primaryIntegralIdeals_inverse_norm_series S (fun r => actualLocalModel r.val K)
  rw [Fintype.prod_unique] at h
  change (∑' J : primaryIntegralIdeals K {p}, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
    (localZinv (actualLocalModel p K).Ring)⁻¹ at h
  rw [← h]
  have he : (∑' J : primaryIntegralIdeals K {p}, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
      ∑' I : PrimaryIdeal K p, (Ideal.absNorm I.1 : ℝ≥0∞)⁻¹ :=
    (primaryIdealSingletonEquiv K p Fact.out).tsum_eq
      (fun I : PrimaryIdeal K p => (Ideal.absNorm I.1 : ℝ≥0∞)⁻¹)
  rw [he]
  convert primary_ideal_inverse_norm_series K (Fact.out : p.Prime) using 1
  apply tsum_congr
  intro I
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.2.1)))]
  simp

theorem actualLocalZ_eq_badPrimeEuler {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : actualLocalZ M = ENNReal.ofReal (badPrimeEuler K (saturationIndex M)) := by
  classical
  unfold actualLocalZ badPrimeEuler
  simp_rw [actual_localZ_eq_idealPrimeEuler]
  rw [ENNReal.ofReal_prod_of_nonneg (fun p hp =>
    (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp)).trans' zero_le_one)]
  exact Finset.prod_coe_sort (saturationIndex M).primeFactors
    (fun p : ℕ => ENNReal.ofReal (idealPrimeEuler K p))

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors

lemma IdealCoprimeTo_primeFactors_iff {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (I : Ideal (𝓞 K)) :
    IdealCoprimeTo q.primeFactors I ↔ (Ideal.absNorm I).Coprime q := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hd hq'
    exact h p (Nat.mem_primeFactors.mpr ⟨hp,hq',hq⟩) hd
  · intro h p hp hd
    have := Nat.eq_one_of_dvd_coprimes h hd (Nat.mem_primeFactors.mp hp).2.1
    exact (Nat.prime_of_mem_primeFactors hp).ne_one this

 
def nonzeroIdealNormFiberEquiv {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : m ≠ 0) :
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m} where
  toFun I := ⟨I.1.1,I.2⟩
  invFun I := ⟨⟨I.1,fun hz => hm (by simpa [hz] using I.2.symm)⟩,I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma integralIdeal_norm_tsum {K : Type*} [Field K] [NumberField K] (F : ℕ → ℝ≥0∞) :
    (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥}, F (Ideal.absNorm I.1)) =
      ∑' m : ℕ, (idealCoefficient K m : ℝ≥0∞) * F m := by
  classical
  rw [← ENNReal.tsum_fiberwise (fun I : {J : Ideal (𝓞 K) // J ≠ ⊥} => F (Ideal.absNorm I.1))
    (fun I => Ideal.absNorm I.1)]
  apply tsum_congr
  intro m
  change (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m},
    F (Ideal.absNorm I.1.1)) = _
  have hf : (fun I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} =>
    F (Ideal.absNorm I.1.1)) = fun _ => F m := by funext I; rw [I.2]
  rw [hf]
  by_cases hm : m = 0
  · subst m
    have : IsEmpty {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = 0} :=
      ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp
  · rw [← (nonzeroIdealNormFiberEquiv (K := K) m hm).symm.tsum_eq]
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, idealCoefficient_pos K m hm,
      Nat.card_eq_fintype_card]
    rfl

def coprimeIdealSubtypeEquiv {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) :
    coprimeIntegralIdeals K q.primeFactors ≃
      {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q} :=
  Equiv.subtypeEquivRight (fun I => IdealCoprimeTo_primeFactors_iff q hq I.1)

 

lemma coprimeIntegralIdeal_norm_tsum {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (F : ℕ → ℝ≥0∞) :
    (∑' I : coprimeIntegralIdeals K q.primeFactors, F (Ideal.absNorm I.1.1)) =
      ∑' m : ℕ, ENNReal.ofReal (coprimeIdealCoefficient K q m) * F m := by
  classical
  have he : (∑' I : coprimeIntegralIdeals K q.primeFactors, F (Ideal.absNorm I.1.1)) =
      ∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q},
        F (Ideal.absNorm I.1.1) := (coprimeIdealSubtypeEquiv (K := K) q hq).tsum_eq
          (fun I => F (Ideal.absNorm I.1.1))
  rw [he]
  have hsub := tsum_subtype
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} | (Ideal.absNorm I.1).Coprime q}
    (fun I => F (Ideal.absNorm I.1))
  simp only [Set.indicator, Set.mem_ofPred_eq] at hsub
  have hsub' : (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q},
      F (Ideal.absNorm I.1.1)) =
    (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
      if (Ideal.absNorm I.1).Coprime q then F (Ideal.absNorm I.1) else 0) := hsub
  rw [hsub']
  rw [integralIdeal_norm_tsum (fun m => if m.Coprime q then F m else 0)]
  apply tsum_congr
  intro m
  change (idealCoefficient K m : ℝ≥0∞) * (if m.Coprime q then F m else 0) =
    ENNReal.ofReal (if m.Coprime q then (idealCoefficient K m : ℝ) else 0) * F m
  split_ifs <;> simp only [mul_zero, zero_mul, ENNReal.ofReal_zero, ENNReal.ofReal_natCast]

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

 
lemma coprimeIdeal_interval_tsum {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (a b d : ℕ) (hd : 0 < d) :
    (∑' J : coprimeIntegralIdeals K q.primeFactors,
      if a < d * Ideal.absNorm J.1.1 ∧ d * Ideal.absNorm J.1.1 ≤ b then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (∑ m ∈ Ioc (a / d) (b / d), coprimeIdealCoefficient K q m) := by
  classical
  rw [coprimeIntegralIdeal_norm_tsum q hq
    (fun m => if a < d*m ∧ d*m ≤ b then (1:ℝ≥0∞) else 0)]
  have hc (m : ℕ) : (a < d*m ∧ d*m ≤ b) ↔ m ∈ Finset.Ioc (a/d) (b/d) := by
    simp only [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, Nat.mul_comm]
  simp_rw [hc, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := Finset.Ioc (a/d) (b/d)) (fun m hm => by simp [hm])]
  simp only [Finset.sum_ite_mem, Finset.inter_self]
  rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => (coprimeIdealCoefficient_bounds K q m).1)]

 
noncomputable def weightedIdealInterval {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b : ℕ) : ℝ≥0∞ :=
  ∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
    if a < Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 ≤ b
    then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0

 

theorem weightedIdealInterval_convolution {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b : ℕ) :
    weightedIdealInterval M a b =
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) := by
  classical
  have h := weighted_ideal_convolution M
    (fun m => if a < m ∧ m ≤ b then (1:ℝ≥0∞) else 0)
  simp only [mul_ite,mul_one,mul_zero] at h
  rw [weightedIdealInterval, h]
  apply tsum_congr
  intro I
  rw [coprimeIdeal_interval_tsum (saturationIndex M) (saturationIndex_ne_zero M) a b _
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2))]

 
theorem primaryIdeal_reciprocal_tail {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (Q : ℝ) (hQ : 0 < Q) (hqQ : (saturationIndex M : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s]; positivity
    (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
      else 0) ≤
        (saturationIndex M : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (localProductConstant n (s / 16) hε) *
          ENNReal.ofReal Q ^ (-s / 16) := by
  dsimp only
  let s : ℝ := 1 / (2 * (n : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have hε : 0 < s / 16 := by positivity
  apply reciprocal_norm_tail_of_moment
    (fun I : primaryIntegralIdeals K (saturationIndex M).primeFactors =>
      globalIdealWeight M (nonzeroIntegralIdealUnit I.1))
    (fun I => (Ideal.absNorm I.1.1 : ℝ≥0∞))
    (fun I => by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2))
    (fun _ => ENNReal.natCast_ne_top _) (saturationIndex M : ℝ≥0∞)
    (ENNReal.ofReal Q) (ENNReal.ofReal (localProductConstant n (s/16) hε))
    (by simpa using hQ) ENNReal.ofReal_ne_top
    (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hqQ) s hs
  have H := primaryIdeal_moment_le M hn hn0 (s/16) hε
  convert H using 1
  rw [ENNReal.ofReal_mul (localProductConstant_pos n (s / 16) hε).le,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hε.le,
    ENNReal.ofReal_natCast]
  exact mul_assoc _ _ _

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma coprimeIdeal_interval_elementary {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (hn : Module.finrank ℤ (𝓞 K) = n) (q a b d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    (∑ m ∈ Ioc (a / d) (b / d), coprimeIdealCoefficient K q m) ≤
      ((b:ℝ)/d) * (1 + Real.log b)^n := by
  have hnonneg : 0 ≤ 1 + Real.log (b : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hb : (1:ℝ) ≤ b)
    linarith
  by_cases hz : b/d = 0
  · simp only [hz,Finset.Ioc_eq_empty_of_le (Nat.zero_le _), sum_empty]
    positivity
  have hpos : 0 < b/d := Nat.pos_of_ne_zero hz
  have hlog : Real.log ((b/d : ℕ):ℝ) ≤ Real.log (b:ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.div_le_self b d)
  have hbase : 0 ≤ 1 + Real.log ((b/d : ℕ):ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hpos : (1:ℝ) ≤ (b/d : ℕ))
    linarith
  calc
    _ ≤ ∑ m ∈ Icc 1 (b/d), coprimeIdealCoefficient K q m := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1), (Finset.mem_Ioc.mp hm).2⟩
      · intro m _ _
        exact (coprimeIdealCoefficient_bounds K q m).1
    _ ≤ ∑ m ∈ Icc 1 (b/d), (nFoldDivisor (n+1) m : ℝ) := by
      apply sum_le_sum
      intro m _
      simpa only [hn] using (coprimeIdealCoefficient_bounds K q m).2
    _ ≤ (b/d : ℕ) * (1+Real.log ((b/d : ℕ):ℝ))^n := nFoldDivisor_summatory_le n (b/d)
    _ ≤ _ := mul_le_mul Nat.cast_div_le (pow_le_pow_left₀ hbase (by linarith) n)
      (pow_nonneg hbase n) (by positivity)

 

theorem weightedIdeal_large_norm_bound {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (a b : ℕ) (hb : 0 < b) (Q : ℝ) (hQ : 0 < Q)
    (hqQ : (saturationIndex M : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s]; positivity
    (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m)
      else 0) ≤
        ENNReal.ofReal ((b:ℝ) * (1+Real.log b)^n) *
          ((saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (localProductConstant n (s / 16) hε) *
            ENNReal.ofReal Q ^ (-s / 16)) := by
  dsimp only
  have hnZ : Module.finrank ℤ (𝓞 K) = n := by
    rw [NumberField.RingOfIntegers.rank]; exact hn
  have hB : 0 ≤ (b:ℝ) * (1+Real.log b)^n := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg
    have := Real.log_nonneg (by exact_mod_cast hb : (1:ℝ) ≤ b)
    linarith
  calc
    _ ≤ ENNReal.ofReal ((b:ℝ)*(1+Real.log b)^n) *
        ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
          if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
          then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
          else 0 := by
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro I
      split_ifs with h
      · have hd : 0 < Ideal.absNorm I.1.1 :=
          Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2)
        have H := ENNReal.ofReal_le_ofReal
          (coprimeIdeal_interval_elementary hnZ (saturationIndex M) a b _ hb hd)
        refine (mul_le_mul_right H _).trans_eq ?_
        rw [show ((b:ℝ)/Ideal.absNorm I.1.1)*(1+Real.log b)^n =
          ((b:ℝ)*(1+Real.log b)^n) / Ideal.absNorm I.1.1 by ring,
          ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hd), ENNReal.ofReal_natCast]
        simp only [div_eq_mul_inv]
        ac_rfl
      · simp
    _ ≤ _ := mul_le_mul_right (primaryIdeal_reciprocal_tail M hn hn0 Q hQ hqQ) _

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_eq_terms (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (NumberField.dedekindZeta K s).re =
      ∑' m : ℕ, realDirichletTerm (idealCoefficientReal K) s m := by
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm

lemma dedekindZeta_real_nonneg (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    0 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  exact tsum_nonneg (realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s)

lemma dedekindZeta_real_antitone (K : Type*) [Field K] [NumberField K]
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    (NumberField.dedekindZeta K t).re ≤ (NumberField.dedekindZeta K s).re := by
  simp only [dedekindZeta_real_eq_terms]
  apply Summable.tsum_le_tsum _ (idealCoefficient_real_summable K (hs.trans_le hst))
    (idealCoefficient_real_summable K hs)
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · change (idealCoefficientReal K m) / (m:ℝ)^t ≤ (idealCoefficientReal K m) / (m:ℝ)^s
    exact div_le_div_of_nonneg_left (idealCoefficientReal_nonneg K m)
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) s)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) hst)

 

lemma dedekindZeta_log_scale_le (K : Type*) [Field K] [NumberField K]
    {u b : ℕ} (hu : 2 ≤ u) (hub : u ≤ b) (hbu : b ≤ u^2) :
    (NumberField.dedekindZeta K (1+1/Real.log u)).re / Real.log u ≤
      2 * (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b := by
  have huR : 0 < Real.log (u:ℝ) := Real.log_pos (by exact_mod_cast hu : (1:ℝ) < u)
  have hbR : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hu.trans hub : (1:ℝ) < b)
  have hlog : Real.log (u:ℝ) ≤ Real.log (b:ℝ) :=
    Real.log_le_log (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hu)
      (by exact_mod_cast hub)
  have hlog2 : Real.log (b:ℝ) ≤ 2*Real.log (u:ℝ) := by
    have H := Real.log_le_log (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (hu.trans hub))
      (show (b:ℝ) ≤ (u:ℝ)^2 by exact_mod_cast hbu)
    simpa only [Real.log_pow, Nat.cast_ofNat] using H
  have hz := dedekindZeta_real_nonneg K (1+1/Real.log b)
  have H := dedekindZeta_real_antitone K
    (show 1 < 1+1/Real.log (b:ℝ) by linarith [one_div_pos.mpr hbR])
    (show 1+1/Real.log (b:ℝ) ≤ 1+1/Real.log (u:ℝ) by
      linarith [one_div_le_one_div_of_le huR hlog])
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one] at H hz
  have hrec : 1/Real.log (u:ℝ) ≤ 2/Real.log (b:ℝ) := by
    apply (div_le_div_iff₀ huR hbR).mpr
    simpa using hlog2
  calc
    _ ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log u :=
      div_le_div_of_nonneg_right H huR.le
    _ ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re * (2/Real.log b) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hrec hz
    _ = _ := by ring

 

theorem coprime_ideal_scaled_interval (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b d : ℕ, 0 < q → 0 < d → Real.log q ≤ (b/d : ℕ) →
          R ≤ b/d → a ≤ b → η*(b/d : ℕ) ≤ (b/d : ℕ)-(a/d : ℕ) →
          b ≤ (b/d)^2 →
          ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d →
          (∑ m ∈ Ioc (a/d) (b/d), coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/d) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
                badPrimeEuler K q := by
  obtain ⟨C,hC,hInt⟩ := coprime_ideal_relative_interval_normalized n
  refine ⟨4*C,by positivity,?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt η hη
  refine ⟨max R 2,?_⟩
  intro K _ _ hn q a b d hq hd hlog hbound hab hrel hsquare hwidth
  have hu : 2 ≤ b/d := (le_max_right R 2).trans hbound
  have H := hR K hn q (a/d) (b/d) hq hlog ((le_max_left R 2).trans hbound)
    (Nat.div_le_div_right hab) hrel
  have hlogu : 0 < Real.log ((b/d : ℕ):ℝ) := Real.log_pos (by exact_mod_cast hu : (1:ℝ) < (b/d:ℕ))
  have hΔ : 0 ≤ ((b:ℝ)-a)/d := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hab)) (Nat.cast_nonneg _)
  have hz := dedekindZeta_real_nonneg K (1+1/Real.log (b/d : ℕ))
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one] at hz
  have hscale := dedekindZeta_log_scale_le K hu (Nat.div_le_self b d) hsquare
  calc
    _ ≤ C * ((((b/d : ℕ):ℝ)-(a/d : ℕ))/Real.log (b/d : ℕ)) *
        (NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / badPrimeEuler K q := H
    _ = (C * (((b/d : ℕ):ℝ)-(a/d : ℕ))) *
        ((NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / Real.log (b/d : ℕ)) /
        badPrimeEuler K q := by ring
    _ ≤ (C * (2*((b:ℝ)-a)/d)) *
        ((NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / Real.log (b/d : ℕ)) /
        badPrimeEuler K q := by
      apply div_le_div_of_nonneg_right _ (badPrimeEuler_pos K q).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hC.le)
        (div_nonneg hz hlogu.le)
    _ ≤ (C * (2*((b:ℝ)-a)/d)) *
        (2 * (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
        badPrimeEuler K q := by
      apply div_le_div_of_nonneg_right _ (badPrimeEuler_pos K q).le
      apply mul_le_mul_of_nonneg_left hscale
      exact mul_nonneg hC.le (by
        simpa only [mul_div_assoc] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hΔ)
    _ = _ := by ring

end PrimeDegreePackets
end
end

end OAI
