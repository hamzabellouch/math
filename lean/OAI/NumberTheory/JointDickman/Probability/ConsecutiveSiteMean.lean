import OAI.NumberTheory.JointDickman.Amplification.ConsecutiveCRT
import OAI.NumberTheory.JointDickman.Probability.PairHitSites

namespace OAI

/-! # Replacing the actual consecutive prime sites by independent sites -/

namespace JointDickman
open Finset

theorem consecutive_site_mean_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ S ∈ P.powerset, ∀ D ∈ P.powerset, |F S D| ≤ L) :
    |(∑ n ∈ range (∏ p ∈ P, p), F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1))) /
        (∏ p ∈ P, (p : ℝ)) -
      ∑ S ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
          bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) D * F S D| ≤
      4*L*∑ p ∈ P, 1 / (p : ℝ)^2 := by
  classical
  let G (x : P → Bool × Bool) := F (hitSites P x).1.val (hitSites P x).2.val
  have hG (x : P → Bool × Bool) : |G x| ≤ L :=
    hF _ (hitSites P x).1.property _ (hitSites P x).2.property
  have hc := consecutive_crt_mean P hP G
  simp only [G, hitSites_consecutive] at hc
  have hi := pairHitSites_sum P (fun p => 1 / (p : ℝ)) F
  have ht := finiteMass_test_bound_of_l1
    (fun x => finiteProductMass (fun p : P => consecutiveHitMass (1 / (p.val : ℝ))) x)
    (fun x => finiteProductMass (fun p : P => independentHitMass (1 / (p.val : ℝ))) x)
    (fun x => (G x : ℂ)) hL
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hG x)
    (consecutive_prime_product_l1 P hP)
  have ht' : |(∑ x, finiteProductMass (fun p : P => consecutiveHitMass (1 / (p.val : ℝ))) x * G x) -
      (∑ x, finiteProductMass (fun p : P => independentHitMass (1 / (p.val : ℝ))) x * G x)| ≤
        L*(4*∑ p ∈ P, 1 / (p : ℝ)^2) := by
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using ht
  rw [hc, ← hi]
  convert ht' using 1; ring

end JointDickman

end OAI
