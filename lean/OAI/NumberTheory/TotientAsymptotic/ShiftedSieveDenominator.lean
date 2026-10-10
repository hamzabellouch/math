import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveModel
import OAI.NumberTheory.TotientAsymptotic.FiniteSieveMass
import OAI.NumberTheory.TotientAsymptotic.MertensLogMass

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def shiftedSieveWeight (b p : ℕ) : ℝ :=
  shiftedSieveDensity b p / (1-shiftedSieveDensity b p)

lemma shiftedSieveWeight_nonneg (b : ℕ) {z p : ℕ} (hp : p ∈ oddSievePrimes z) :
    0 ≤ shiftedSieveWeight b p := by
  obtain ⟨_,hpp,hp2⟩ := mem_oddSievePrimes.mp hp
  exact div_nonneg (shiftedSieveDensity_positive b p hpp).le
    (sub_pos.mpr (shiftedSieveDensity_lt_one b p hpp hp2)).le

lemma shiftedSieveWeight_moment (b : ℕ) {z p : ℕ} (hp : p ∈ oddSievePrimes z) :
    shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p) =
      shiftedSieveDensity b p * Real.log p := by
  obtain ⟨_,hpp,hp2⟩ := mem_oddSievePrimes.mp hp
  have hn : 1-shiftedSieveDensity b p ≠ 0 :=
    (sub_pos.mpr (shiftedSieveDensity_lt_one b p hpp hp2)).ne'
  have hn' : 1+shiftedSieveWeight b p ≠ 0 := by
    have := shiftedSieveWeight_nonneg b hp
    linarith
  unfold shiftedSieveWeight
  field_simp
  ring

lemma shiftedSieve_moment_le (b z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ oddSievePrimes z,
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p)) ≤
        2*Real.log 4*(2+Real.log z) := by
  have hpoint (p : ℕ) (hp : p ∈ oddSievePrimes z) :
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p) ≤
        2*(Real.log p/(p:ℝ)) := by
    obtain ⟨_,hpp,_⟩ := mem_oddSievePrimes.mp hp
    rw [shiftedSieveWeight_moment b hp,shiftedSieveDensity_prime b p hpp]
    have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs <;> simp only [div_eq_mul_inv] <;> nlinarith [mul_nonneg (inv_nonneg.mpr hp0.le) hl]
  calc
    _ ≤ ∑ p ∈ oddSievePrimes z,2*(Real.log p/(p:ℝ)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,2*(Real.log p/(p:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpz,hpp,_⟩ := mem_oddSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le,hpz⟩,hpp⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact mul_nonneg (by norm_num) (div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      nlinarith [prime_log_mass_le z hz]

lemma shiftedSieveTerms_prod (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ oddSievePrimes z) :
    selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,shiftedSieveWeight b p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_oddSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_oddSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change shiftedSieveDensity b p * (1/(1-shiftedSieveDensity b p)) = _
  simp [shiftedSieveWeight,div_eq_mul_inv]

lemma shiftedSieveBoundingSum_powerset (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (shiftedPrimeSieve b X z y hy) =
      ∑ T ∈ (oddSievePrimes z).powerset,
        if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,shiftedSieveWeight b p else 0 := by
  classical
  have hsq := oddSievePrimes_prod_squarefree z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ oddSievePrimes z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then
      selbergTerms (shiftedPrimeSieve b X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_oddSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [shiftedSieveTerms_prod b X z y hy T (Finset.mem_powerset.mp hT)]

/-- The logarithmic first moment confines at least half of the Euler product to
integers within the square-root cutoff used by Selberg's denominator. -/
theorem shiftedSieveBoundingSum_lower (b X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 8*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p))/2 ≤
      selbergBoundingSum (shiftedPrimeSieve b X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y / 2 := by positivity
  have hm : (∑ p ∈ oddSievePrimes z,
      shiftedSieveWeight b p * Real.log p / (1+shiftedSieveWeight b p)) ≤
        (Real.log y/2)/2 := by
    nlinarith [shiftedSieve_moment_le b z hz]
  have hh := subset_weight_below_half (oddSievePrimes z) (shiftedSieveWeight b)
    (fun p => Real.log p) (fun p hp => shiftedSieveWeight_nonneg b hp)
    (fun p hp => Real.log_nonneg (by
      exact_mod_cast (mem_oddSievePrimes.mp hp).2.1.one_lt.le)) hl hm
  apply hh.trans
  rw [shiftedSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_oddSievePrimes.mp (hTp hp)).2.1
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
  · exact Finset.prod_nonneg (fun p hp => shiftedSieveWeight_nonneg b (hTp hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
