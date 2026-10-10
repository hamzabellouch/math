import OAI.NumberTheory.TwoPoint.Bounds.SmoothReciprocalMass

namespace OAI

/-! Elementary bounds for the Euler cost of adjoining retained tuple primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma one_le_smoothReciprocalProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    1 ≤ smoothReciprocalProduct P s := by
  apply one_le_prod₀
  intro p hp
  have hr : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  exact (one_le_inv₀ (sub_pos.mpr hr)).mpr (by
    have hh := Real.rpow_nonneg (Nat.cast_nonneg p) (-s)
    linarith)

lemma smoothReciprocalProduct_union_le (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (s : ℝ) (hs : 0 < s) :
    smoothReciprocalProduct (P ∪ Q) s ≤
      smoothReciprocalProduct P s * smoothReciprocalProduct Q s := by
  have he : smoothReciprocalProduct (P ∪ Q) s * smoothReciprocalProduct (P ∩ Q) s =
      smoothReciprocalProduct P s * smoothReciprocalProduct Q s := by
    exact prod_union_inter
  have hnonneg := smoothReciprocalProduct_nonneg (P ∪ Q)
    (fun p hp => (mem_union.mp hp).elim (hP p) (hQ p)) s hs
  have hone := one_le_smoothReciprocalProduct (P ∩ Q)
    (fun p hp => hP p (mem_inter.mp hp).1) s hs
  exact (le_mul_of_one_le_right hnonneg hone).trans_eq he

lemma smoothReciprocalProduct_mul_le (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (s : ℝ) (hs : 0 < s) :
    smoothReciprocalProduct (q * t).primeFactors s ≤
      smoothReciprocalProduct q.primeFactors s * smoothReciprocalProduct t.primeFactors s := by
  rw [Nat.primeFactors_mul hq.ne' ht.ne']
  exact smoothReciprocalProduct_union_le _ _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) s hs

lemma reciprocal_one_sub_le_exp (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    (1 - r)⁻¹ ≤ Real.exp (2 * r) := by
  have hd : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 1 + 2 * r := by
    have hh : 1 / (1 - r) ≤ 1 + 2 * r := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg hr (show 0 ≤ 1 - 2 * r by linarith)])
    simpa only [one_div] using hh
  exact hinv.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * r))

lemma smooth_half_product_exp_bound (P : Finset ℕ)
    (hsmall : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤
      Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp (2 * (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
      apply prod_le_prod₀
      · intro p hp
        apply inv_nonneg.mpr
        have hh := hsmall p hp
        linarith
      · intro p hp
        exact reciprocal_one_sub_le_exp _ (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hsmall p hp)
    _ = _ := by rw [← Real.exp_sum, mul_sum]

lemma smooth_half_product_le_two (P : Finset ℕ)
    (hsmall : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2)
    (hsum : 2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ Real.log 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  exact (smooth_half_product_exp_bound P hsmall).trans
    ((Real.exp_le_exp.mpr hsum).trans_eq (Real.exp_log (by norm_num)))

end TwoPointCorrelations

end OAI
