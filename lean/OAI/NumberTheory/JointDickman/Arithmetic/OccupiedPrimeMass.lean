import OAI.NumberTheory.JointDickman.Amplification.RestrictedRootMass
import OAI.NumberTheory.JointDickman.Probability.SitePartition

namespace OAI

/-! # Reciprocal mass of occupied primes in independent endpoint sites -/

namespace JointDickman
open Finset PublishedInputs

theorem finiteExpectation_finset_sum {Ω ι : Type*} [Fintype Ω]
    (w : Ω → ℝ) (I : Finset ι) (f : ι → Ω → ℝ) :
    finiteExpectation w (fun x => ∑ i ∈ I, f i x) = ∑ i ∈ I, finiteExpectation w (f i) := by
  unfold finiteExpectation
  simp only [mul_sum]
  exact sum_comm

open Classical in
noncomputable def occupiedPrimeReciprocalMass {M : ℕ} (B : ℕ) (S : Fin M → Finset ℕ) : ℝ :=
  ∑ p ∈ auxiliaryPrimes B, if ∃ i, p ∈ S i then 1/(p : ℝ) else 0

open Classical in
theorem independent_site_prime_hit {B M : ℕ} {p : ℕ} (hp : p ∈ auxiliaryPrimes B) (i : Fin M) :
    finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => p ∈ (S i).val) = 1/(p : ℝ) := by
  rw [finiteProbability_eq_indicator_mean]
  have hc := siteProduct_expectation_coordinate (fun _ : Fin M => independentPrimeSetMass B)
    (fun _ => independentPrimeSetMass_sum B) i
    (fun R => if p ∈ R.val then (1 : ℝ) else 0)
  have hm := bernoulliSubsetMass_hit (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) hp
  rw [finiteProbability_eq_indicator_mean] at hm
  trans finiteExpectation (independentPrimeSetMass B) (fun R => if p ∈ R.val then (1 : ℝ) else 0)
  · convert hc using 1
    apply congrArg (finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)))
    funext S
    by_cases hs : p ∈ (S i).val <;> simp [hs]
  · convert hm using 1
    apply congrArg (finiteExpectation (independentPrimeSetMass B))
    funext R
    by_cases hs : p ∈ R.val <;> simp [hs]

open Classical in
theorem independent_occupied_prime_probability {B M : ℕ} {p : ℕ}
    (hp : p ∈ auxiliaryPrimes B) :
    finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => ∃ i, p ∈ (S i).val) ≤ (M : ℝ)/(p : ℝ) := by
  calc
    _ ≤ ∑ i : Fin M, finiteProbability
        (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => p ∈ (S i).val) := finiteProbability_union_le _
      (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) _
    _ = _ := by simp_rw [independent_site_prime_hit hp]; simp [div_eq_mul_inv]

open Classical in
/-- The candidate family need not be independent of occupied primes:
this estimate controls their entire reciprocal mass before using its
deterministic candidate-count bound. -/
theorem independent_occupied_prime_mass (B M : ℕ) :
    finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => occupiedPrimeReciprocalMass B (fun i => (S i).val)) ≤
      (M : ℝ)*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) := by
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have he (p : ℕ) : finiteExpectation w
      (fun S => if ∃ i, p ∈ (S i).val then 1/(p : ℝ) else 0) =
      (1/(p : ℝ))*finiteProbability w (fun S => ∃ i, p ∈ (S i).val) := by
    unfold finiteExpectation finiteProbability
    dsimp only
    rw [mul_sum]
    apply sum_congr rfl
    intro S _
    by_cases hs : ∃ i, p ∈ (S i).val <;> simp [hs,mul_comm]
  unfold occupiedPrimeReciprocalMass
  rw [finiteExpectation_finset_sum]
  calc
    _ = ∑ p ∈ auxiliaryPrimes B,
        (1/(p : ℝ))*finiteProbability w (fun S => ∃ i, p ∈ (S i).val) := sum_congr rfl (fun p _ => he p)
    _ ≤ ∑ p ∈ auxiliaryPrimes B, (1/(p : ℝ))*((M : ℝ)/(p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (independent_occupied_prime_probability hp) (by positivity)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring

end JointDickman

end OAI
