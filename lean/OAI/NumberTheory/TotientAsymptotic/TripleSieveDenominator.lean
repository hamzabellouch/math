import OAI.NumberTheory.TotientAsymptotic.TripleSieveModel
import OAI.NumberTheory.TotientAsymptotic.FiniteSieveMass
import OAI.NumberTheory.TotientAsymptotic.MertensLogMass

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def tripleSieveWeight (a b p : ℕ) : ℝ :=
  tripleSieveDensity a b p / (1-tripleSieveDensity a b p)

lemma tripleSieveWeight_nonneg (a b : ℕ) {z p : ℕ} (hp : p ∈ tripleSievePrimes z) :
    0 ≤ tripleSieveWeight a b p := by
  obtain ⟨_,hpp,hp2⟩ := mem_tripleSievePrimes.mp hp
  exact div_nonneg (tripleSieveDensity_positive a b p hpp).le
    (sub_pos.mpr (tripleSieveDensity_lt_one a b p hpp hp2)).le

lemma tripleSieveWeight_moment (a b : ℕ) {z p : ℕ} (hp : p ∈ tripleSievePrimes z) :
    tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p) =
      tripleSieveDensity a b p * Real.log p := by
  obtain ⟨_,hpp,hp2⟩ := mem_tripleSievePrimes.mp hp
  have hn : 1-tripleSieveDensity a b p ≠ 0 :=
    (sub_pos.mpr (tripleSieveDensity_lt_one a b p hpp hp2)).ne'
  have hn' : 1+tripleSieveWeight a b p ≠ 0 := by
    have := tripleSieveWeight_nonneg a b hp
    linarith
  unfold tripleSieveWeight
  field_simp
  ring

lemma tripleSieve_moment_le (a b z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ tripleSievePrimes z,
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p)) ≤
        3*Real.log 4*(2+Real.log z) := by
  have hpoint (p : ℕ) (hp : p ∈ tripleSievePrimes z) :
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p) ≤
        3*(Real.log p/(p:ℝ)) := by
    obtain ⟨_,hpp,_⟩ := mem_tripleSievePrimes.mp hp
    rw [tripleSieveWeight_moment a b hp,tripleSieveDensity_prime a b p hpp]
    let _ : Fact p.Prime := ⟨hpp⟩
    rw [tripleRootCount_eq_card]
    have hc : ((tripleSieveRoots p a b).card:ℝ) ≤ 3 := by
      exact_mod_cast tripleSieveRoots_card_le p a b
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hh := mul_le_mul_of_nonneg_right hc (div_nonneg hl hp0.le)
    convert hh using 1
    ring

  calc
    _ ≤ ∑ p ∈ tripleSievePrimes z,3*(Real.log p/(p:ℝ)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,3*(Real.log p/(p:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpz,hpp,_⟩ := mem_tripleSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le,hpz⟩,hpp⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact mul_nonneg (by norm_num) (div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      nlinarith [prime_log_mass_le z hz]

lemma tripleSieveTerms_prod (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ tripleSievePrimes z) :
    selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,tripleSieveWeight a b p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_tripleSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_tripleSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change tripleSieveDensity a b p * (1/(1-tripleSieveDensity a b p)) = _
  simp [tripleSieveWeight,div_eq_mul_inv]

lemma tripleSieveBoundingSum_powerset (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (triplePrimeSieve a b X z y hy) =
      ∑ T ∈ (tripleSievePrimes z).powerset,
        if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,tripleSieveWeight a b p else 0 := by
  classical
  have hsq := tripleSievePrimes_squarefree z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ tripleSievePrimes z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ tripleSievePrimes z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then
      selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_tripleSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [tripleSieveTerms_prod a b X z y hy T (Finset.mem_powerset.mp hT)]

/-- The logarithmic first moment confines at least half of the Euler product to
integers within the square-root cutoff used by Selberg's denominator. -/
theorem tripleSieveBoundingSum_lower (a b X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 12*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))/2 ≤
      selbergBoundingSum (triplePrimeSieve a b X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y / 2 := by positivity
  have hm : (∑ p ∈ tripleSievePrimes z,
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p)) ≤
        (Real.log y/2)/2 := by
    nlinarith [tripleSieve_moment_le a b z hz]
  have hh := subset_weight_below_half (tripleSievePrimes z) (tripleSieveWeight a b)
    (fun p => Real.log p) (fun p hp => tripleSieveWeight_nonneg a b hp)
    (fun p hp => Real.log_nonneg (by
      exact_mod_cast (mem_tripleSievePrimes.mp hp).2.1.one_lt.le)) hl hm
  apply hh.trans
  rw [tripleSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_tripleSievePrimes.mp (hTp hp)).2.1
  have hpos : (0:ℝ) < (∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hlog : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
    rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
  split_ifs with hsmall hcut hcut
  · exact le_rfl
  · exfalso
    apply hcut
    apply (Real.log_le_log_iff (sq_pos_of_pos hpos) (by linarith : 0<y)).mp
    rw [Real.log_pow,hlog]
    norm_num
    linarith
  · exact Finset.prod_nonneg (fun p hp => tripleSieveWeight_nonneg a b (hTp hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
