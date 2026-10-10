import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSquareMean
import Mathlib.Data.Nat.GCD.Basic

namespace OAI

/-! The divisor-square estimate in the mixed prime/cofactor moment.
The map `(d,e) ↦ (gcd(d,e), d/gcd(d,e), e/gcd(d,e))` bounds a pair of
supported divisors by three supported factors whose product divides the
integer. Summing the divisibility tests gives a finite Euler majorant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def mrtGcdTriple (v : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (Nat.gcd v.1 v.2, (v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2))

lemma mrt_gcd_triple_left (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.1 = v.1 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

lemma mrt_gcd_triple_right (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.2 = v.2 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

lemma mrt_gcd_triple_injective : Function.Injective mrtGcdTriple := by
  intro v w h
  apply Prod.ext
  · rw [← mrt_gcd_triple_left v, ← mrt_gcd_triple_left w, h]
  · rw [← mrt_gcd_triple_right v, ← mrt_gcd_triple_right w, h]

lemma mrt_gcd_triple_product {d e : ℕ} (hd : 0 < d) :
    (mrtGcdTriple (d, e)).1 *
      ((mrtGcdTriple (d, e)).2.1 * (mrtGcdTriple (d, e)).2.2) = Nat.lcm d e := by
  change Nat.gcd d e * (d / Nat.gcd d e * (e / Nat.gcd d e)) = _
  apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left e hd)
  calc
    _ = (Nat.gcd d e * (d / Nat.gcd d e)) *
        (Nat.gcd d e * (e / Nat.gcd d e)) := by ring
    _ = d * e := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
    _ = Nat.gcd d e * Nat.lcm d e := (Nat.gcd_mul_lcm d e).symm

/-- A finite divisor-closed positive set suffices; no asymptotic sieve
or mean-value theorem is hidden in the combinatorial estimate. -/
theorem mrt_divisor_pair_card (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (n : ℕ) :
    ((S.filter (fun d => d ∣ n)).card) ^ 2 ≤
      ((S ×ˢ (S ×ˢ S)).filter (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card := by
  let D := S.filter (fun d => d ∣ n)
  have hm : ∀ v ∈ D ×ˢ D,
      mrtGcdTriple v ∈ (S ×ˢ (S ×ˢ S)).filter
        (fun w => w.1 * (w.2.1 * w.2.2) ∣ n) := by
    rintro ⟨d, e⟩ hv
    obtain ⟨hd, he⟩ := mem_product.mp hv
    obtain ⟨hdS, hdn⟩ := mem_filter.mp hd
    obtain ⟨heS, hen⟩ := mem_filter.mp he
    have hd0 := hS d hdS
    have he0 := hS e heS
    have hg0 := Nat.gcd_pos_of_pos_left e hd0
    have hgd := Nat.gcd_dvd_left d e
    have hge := Nat.gcd_dvd_right d e
    have hqd : 0 < d / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd hd0 hgd) hg0
    have hqe : 0 < e / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd he0 hge) hg0
    apply mem_filter.mpr
    constructor
    · exact mem_product.mpr ⟨hclosed d hdS _ hg0 hgd, mem_product.mpr
        ⟨hclosed d hdS _ hqd (Nat.div_dvd_of_dvd hgd),
          hclosed e heS _ hqe (Nat.div_dvd_of_dvd hge)⟩⟩
    · rw [mrt_gcd_triple_product hd0]
      exact Nat.lcm_dvd hdn hen
  have hc := card_le_card_of_injOn mrtGcdTriple hm
    (fun _ _ _ _ h => mrt_gcd_triple_injective h)
  simpa only [card_product, pow_two] using hc

theorem mrt_divisor_count_second_moment (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2) ≤
      (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
  let K := S ×ˢ (S ×ˢ S)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ v ∈ K,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n _
      have hc := mrt_divisor_pair_card S hS hclosed n
      have hcR : ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2 ≤
          (((S ×ˢ (S ×ˢ S)).filter
            (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card : ℝ) := by exact_mod_cast hc
      simpa only [sum_boole] using hcR
    _ = ∑ v ∈ K, ∑ n ∈ Icc 1 N,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ v ∈ K, (N : ℝ) / (v.1 * (v.2.1 * v.2.2) : ℕ) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨h1, h23⟩ := mem_product.mp hv
      obtain ⟨h2, h3⟩ := mem_product.mp h23
      rw [mrt_count_multiples (Nat.mul_pos (hS _ h1) (Nat.mul_pos (hS _ h2) (hS _ h3)))]
      exact Nat.cast_div_le
    _ = (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
      simp only [K, sum_product, Nat.cast_mul, ← div_div]
      simp_rw [div_eq_mul_inv]
      simp only [← mul_sum, ← sum_mul]
      ring

end TwoPointCorrelations

end OAI
