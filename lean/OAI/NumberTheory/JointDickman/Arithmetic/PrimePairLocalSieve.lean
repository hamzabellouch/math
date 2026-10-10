import Mathlib

namespace OAI

/-! # Local factors for the prime-pair upper sieve -/
namespace JointDickman
open Finset

noncomputable def primePairRoots (p h : ℕ) : Finset (ZMod p) := {0,-(h:ZMod p)}

lemma primePairRoots_card (p h : ℕ) :
    (primePairRoots p h).card = if p ∣ h then 1 else 2 := by
  classical
  by_cases hh : p ∣ h
  · have hz : (h:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hh
    simp [primePairRoots,hz,hh]
  · have hz : (h:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff h p).mp hh
    simp [primePairRoots,hh,hz]

lemma primePairRoots_mem (p h n : ℕ) :
    (n:ZMod p) ∈ primePairRoots p h ↔ p ∣ n ∨ p ∣ n+h := by
  classical
  simp only [primePairRoots,mem_insert,mem_singleton]
  rw [ZMod.natCast_eq_zero_iff]
  have he : (n:ZMod p) = -(h:ZMod p) ↔ p ∣ n+h := by
    rw [eq_neg_iff_add_eq_zero,←Nat.cast_add,ZMod.natCast_eq_zero_iff]
  exact or_congr_right he

lemma primePair_local_factor_bound {p h : ℕ} (hp : p.Prime) :
    0 ≤ 1-((primePairRoots p h).card:ℝ)/(p:ℝ) ∧
    1-((primePairRoots p h).card:ℝ)/(p:ℝ) ≤
      (1-1/(p:ℝ))^2*(if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hu : 0 < 1-1/(p:ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hp0).mpr (by linarith)
  rw [primePairRoots_card]
  split_ifs with hh
  · norm_num only [Nat.cast_one]
    constructor
    · exact hu.le
    · have he : (1-1/(p:ℝ))^2*(1-1/(p:ℝ))⁻¹ = 1-1/(p:ℝ) := by field_simp
      rw [he]
  · norm_num only [Nat.cast_ofNat,mul_one]
    constructor
    · exact sub_nonneg.mpr ((div_le_one hp0).mpr hp2)
    · simp only [div_eq_mul_inv,one_mul]
      nlinarith [sq_nonneg ((p:ℝ)⁻¹)]

lemma primePair_local_product_bound {P : Finset ℕ} {h : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hh : 0 < h) :
    (∏ p ∈ P, (1-((primePairRoots p h).card:ℝ)/(p:ℝ))) ≤
      (h:ℝ)/h.totient * (∏ p ∈ P, (1-1/(p:ℝ)))^2 := by
  classical
  have hfactor (p : ℕ) (hp : p.Prime) : 0 < 1-1/(p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hsub : P.filter (fun p => p ∣ h) ⊆ h.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2,hh.ne'⟩
  have hprod : (∏ p ∈ P, if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) ≤
      ∏ p ∈ h.primeFactors, (1-1/(p:ℝ))⁻¹ := by
    rw [←prod_filter]
    apply prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hp
      exact inv_nonneg.mpr (hfactor p (Nat.prime_of_mem_primeFactors (hsub hp))).le
    · intro p hp _
      apply (one_le_inv₀ (hfactor p (Nat.prime_of_mem_primeFactors hp))).mpr
      exact sub_le_self _ (by positivity)
  have htot : (h:ℝ)/h.totient = ∏ p ∈ h.primeFactors, (1-1/(p:ℝ))⁻¹ := by
    have he := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors h)
    have he' : (h.totient:ℝ) = (h:ℝ)*∏ p ∈ h.primeFactors, (1-1/(p:ℝ)) := by
      simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,Rat.cast_one,Rat.cast_inv,one_div] using he
    have hhp : (0:ℝ) < ∏ p ∈ h.primeFactors, (1-1/(p:ℝ)) :=
      prod_pos (fun p hp => hfactor p (Nat.prime_of_mem_primeFactors hp))
    rw [he',prod_inv_distrib]
    have hh0 : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  calc
    _ ≤ ∏ p ∈ P, ((1-1/(p:ℝ))^2*(if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1)) :=
      prod_le_prod₀ (fun p hp => (primePair_local_factor_bound (hP p hp)).1)
        (fun p hp => (primePair_local_factor_bound (hP p hp)).2)
    _ = (∏ p ∈ P, (1-1/(p:ℝ)))^2 *
        (∏ p ∈ P, if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) := by rw [prod_mul_distrib,prod_pow]
    _ ≤ (∏ p ∈ P, (1-1/(p:ℝ)))^2 * ((h:ℝ)/h.totient) :=
      mul_le_mul_of_nonneg_left (hprod.trans_eq htot.symm) (sq_nonneg _)
    _ = _ := mul_comm _ _

end JointDickman

end OAI
