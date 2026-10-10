import OAI.NumberTheory.TotientAsymptotic.SquarefreeIntervalMass

namespace OAI

/-! The lower-factor-count tail used in Ford's upper count of totient values. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma squarefree_lower_factor_mass (S Q : Finset ℕ) {c R H : ℝ} (hc : 1 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S ∧ R ≤ (n.primeFactors.card:ℝ))
    (hH : (∑ p ∈ S,(p:ℝ)⁻¹) ≤ H) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp (c*H-R*Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm := squarefree_reciprocal_moment S Q hc0.le
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have ht : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ c^(-R)*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hpow := Real.rpow_le_rpow_of_exponent_le hc (hQ n hn).2.2
    rw [Real.rpow_natCast] at hpow
    have he : c^(-R)*c^R=1 := by
      rw [← Real.rpow_add hc0]
      simp
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hc0.le (-R))
    rw [he] at hh
    have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ (n:ℝ)⁻¹ by positivity)
    simpa only [div_eq_mul_inv,mul_assoc,one_mul] using hmul
  calc
    _ ≤ c^(-R)*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := ht
    _ ≤ c^(-R)*Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hc0.le (-R))
    _ ≤ c^(-R)*Real.exp (c*H) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc0.le (-R))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hH hc0.le)
    _ = _ := by
      rw [Real.rpow_def_of_pos hc0,← Real.exp_add]
      congr 1
      ring

theorem squarefree_band_lower_mass : ∃ D : ℝ,0 < D ∧
    ∀ U V c R : ℝ,2 ≤ U → U ≤ V → 1 ≤ c → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,Squarefree n ∧
      (∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) ∧
      R ≤ (n.primeFactorsList.length:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp (c*(B V-B U+D)-R*Real.log c) := by
  obtain ⟨D,hD,hprime⟩ := prime_interval_upper_bounded_error
  refine ⟨D,hD,?_⟩
  intro U V c R hU hUV hc Q hQ
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  apply squarefree_lower_factor_mass S Q hc _ (hprime U V hU hUV)
  intro n hn
  refine ⟨(hQ n hn).1,?_,?_⟩
  · intro p hp
    have hp' : p ∈ n.primeFactorsList := List.mem_toFinset.mp hp
    have hb := (hQ n hn).2.1 p hp'
    exact Finset.mem_filter.mpr ⟨(primesUpTo_mem (by linarith : 0 ≤ V)).mpr
      ⟨Nat.prime_of_mem_primeFactorsList hp',hb.2⟩,hb.1⟩
  · rw [squarefree_primeFactors_card (hQ n hn).1]
    exact (hQ n hn).2.2

end TotientAsymptotic

end

end OAI
