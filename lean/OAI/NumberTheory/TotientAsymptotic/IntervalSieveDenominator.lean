import OAI.NumberTheory.TotientAsymptotic.IntervalSieveModel
import OAI.NumberTheory.TotientAsymptotic.FiniteSieveMass
import OAI.NumberTheory.TotientAsymptotic.MertensLogMass

namespace OAI

/-! The interval sieve has the reciprocal Euler-product denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def intervalSieveWeight (p : ℕ) : ℝ := 1/((p:ℝ)-1)

lemma intervalSieveWeight_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ intervalSieveWeight p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg zero_le_one (by linarith)

lemma intervalSieveWeight_density {p : ℕ} (hp : p.Prime) :
    intervalSieveWeight p = intervalSieveDensity p/(1-intervalSieveDensity p) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  rw [intervalSieveDensity_prime hp]
  dsimp [intervalSieveWeight]
  field_simp

lemma intervalSieveWeight_moment {p : ℕ} (hp : p.Prime) :
    intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p) = Real.log p/p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p:ℝ)-1 ≠ 0 := by linarith
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have he : 1+intervalSieveWeight p = (p:ℝ)/(p-1) := by
    unfold intervalSieveWeight
    field_simp
    ring
  rw [he]
  dsimp [intervalSieveWeight]
  field_simp

lemma intervalSieve_moment_le (S z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ intervalSievePrimes S z,
      intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p)) ≤
        Real.log 4*(2+Real.log z) := by
  calc
    _ = ∑ p ∈ intervalSievePrimes S z,Real.log p/p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact intervalSieveWeight_moment (mem_intervalSievePrimes.mp hp).2.1
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,Real.log p/p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hh := mem_intervalSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hh.2.1.two_le,hh.1⟩,hh.2.1⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _)
    _ ≤ _ := prime_log_mass_le z hz

lemma intervalSieveTerms_prod (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ intervalSievePrimes S z) :
    selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,intervalSieveWeight p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_intervalSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_intervalSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change intervalSieveDensity p*(1/(1-intervalSieveDensity p)) = _
  rw [intervalSieveWeight_density hpp]
  ring

lemma intervalSieveBoundingSum_powerset (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (intervalPrimeSieve S X z y hy) =
      ∑ T ∈ (intervalSievePrimes S z).powerset,
        if ((∏ p ∈ T,p:ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,intervalSieveWeight p else 0 := by
  classical
  have hsq := intervalSieve_squarefree S z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ intervalSievePrimes S z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ intervalSievePrimes S z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p:ℕ):ℝ)^2 ≤ y then
      selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_intervalSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [intervalSieveTerms_prod S X z y hy T (Finset.mem_powerset.mp hT)]

theorem intervalSieveBoundingSum_lower (S X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 4*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p))/2 ≤
      selbergBoundingSum (intervalPrimeSieve S X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y/2 := by positivity
  have hm : (∑ p ∈ intervalSievePrimes S z,
      intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p)) ≤ (Real.log y/2)/2 := by
    nlinarith [intervalSieve_moment_le S z hz]
  have hh := subset_weight_below_half (intervalSievePrimes S z) intervalSieveWeight
    (fun p => Real.log p)
    (fun p hp => intervalSieveWeight_nonneg (mem_intervalSievePrimes.mp hp).2.1)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (mem_intervalSievePrimes.mp hp).2.1.one_lt.le))
    hl hm
  apply hh.trans
  rw [intervalSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_intervalSievePrimes.mp (hTp hp)).2.1
  have hpos : (0:ℝ) < (∏ p ∈ T,p:ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hlog : Real.log ((∏ p ∈ T,p:ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
    rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
  split_ifs with hsmall hcut hcut
  · exact le_rfl
  · exfalso
    apply hcut
    apply (Real.log_le_log_iff (sq_pos_of_pos hpos) (by linarith : 0<y)).mp
    rw [Real.log_pow,hlog]
    norm_num
    linarith
  · exact Finset.prod_nonneg (fun p hp => intervalSieveWeight_nonneg (hprimes p hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
