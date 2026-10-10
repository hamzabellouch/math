import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductLocalLaw
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeNormalizerUpper

namespace OAI

/-!
# Small prime products and absent large primes

A small product must omit every prime above its size. Independence turns
this observation into an exact all-absent product bound.
-/

namespace JointDickman

open Finset

open Classical in
theorem bernoulliSubsetMass_subset_sum (P A : Finset ℕ) (q : ℕ → ℝ) :
    (∑ S ∈ P.powerset, if S ⊆ A then bernoulliSubsetMass P q S else 0) =
      ∏ p ∈ P \ A, (1 - q p) := by
  let v := fun p : ℕ => if p ∈ A then (1 : ℝ) else 0
  have hv (S : Finset ℕ) : (∏ p ∈ S, v p) = if S ⊆ A then 1 else 0 := by
    by_cases hS : S ⊆ A
    · simp only [ite_eq_left hS]
      exact prod_eq_one (fun p hp => ite_eq_left (hS hp))
    · rw [ite_eq_right hS]
      obtain ⟨p, hpS, hpA⟩ := not_subset.mp hS
      exact prod_eq_zero hpS (ite_eq_right hpA)
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * ∏ p ∈ S, v p := by
      apply sum_congr rfl
      intro S _
      rw [hv]
      split_ifs <;> simp
    _ = ∏ p ∈ P, (1 - q p + q p * v p) := bernoulliSubsetMass_tilt P q v
    _ = ∏ p ∈ P, if p ∈ A then 1 else (1 - q p) := by
      apply prod_congr rfl
      intro p _
      dsimp [v]
      split_ifs <;> ring
    _ = _ := by
      rw [prod_ite]
      simp only [prod_const_one, one_mul]
      congr 1
      ext p
      simp

open Classical in
theorem primeProduct_small_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z X : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑ S ∈ P.powerset, if (∏ p ∈ S, p : ℕ) ≤ X then
      bernoulliSubsetMass P (fun p => z / p) S else 0) ≤
      primeNormalizer (P.filter (fun p => X < (p : ℝ))) z := by
  let A : Finset ℕ := P.filter (fun (p : ℕ) => (p : ℝ) ≤ X)
  have hq : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨div_nonneg hz hp0.le, (div_le_one hp0).mpr (hz1.trans hp1)⟩
  calc
    _ ≤ ∑ S ∈ P.powerset, if S ⊆ A then bernoulliSubsetMass P (fun p => z / p) S else 0 := by
      apply sum_le_sum
      intro S hSP
      have hS := mem_powerset.mp hSP
      by_cases hsmall : (∏ p ∈ S, p : ℕ) ≤ X
      · have hSA : S ⊆ A := by
          intro p hp
          have hprod : p ≤ ∏ q ∈ S, q := single_le_prod (fun q hq => (hP q (hS hq)).one_le) hp
          exact mem_filter.mpr ⟨hS hp, (by exact_mod_cast hprod : (p : ℝ) ≤ ∏ q ∈ S, q).trans hsmall⟩
        rw [ite_eq_left hsmall, ite_eq_left hSA]
      · rw [ite_eq_right hsmall]
        split_ifs
        · exact bernoulliSubsetMass_nonneg hS hq
        · rfl
    _ = ∏ p ∈ P \ A, (1 - z / (p : ℝ)) := bernoulliSubsetMass_subset_sum P A _
    _ = _ := by
      unfold primeNormalizer
      congr 1
      ext p
      simp [A]
      tauto

open Filter
open scoped Topology

open Classical in
/-- The manuscript's uniform small-log-product tail, including the empty product. -/
theorem primeProduct_small_log_tail
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        if Real.log (∏ p ∈ S, p : ℕ) / B ≤ δ then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0) ≤
        C * (δ + 1 / auxiliaryRatio B) ^ z := by
  obtain ⟨C, hC, hnormalizer⟩ := primeNormalizer_upper hM
  refine ⟨C, hC, ?_⟩
  have hN : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  filter_upwards [hN, auxiliaryCutoff_le_upper, eventually_gt_atTop 1] with B hNB hupper hB
  intro δ hδ hδ1
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hNreal : (2 : ℝ) ≤ auxiliaryCutoff B := by exact_mod_cast hNB
  let X := max (auxiliaryCutoff B : ℝ) (Real.exp (δ * B))
  have hX : 2 ≤ X := hNreal.trans (le_max_left _ _)
  have hXY : X ≤ auxiliaryUpper B := by
    apply max_le hupper
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfilter : (auxiliaryPrimes B).filter (fun (p : ℕ) => Real.exp (δ * B) < (p : ℝ)) =
      largePrimeSet (auxiliaryUpper B) X := by
    ext p
    simp [auxiliaryPrimes, largePrimeSet, X, max_lt_iff, and_assoc]
  have hsmall := primeProduct_small_bound (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (X := Real.exp (δ * B)) hz hz1
  rw [hfilter] at hsmall
  have hevent : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if Real.log (∏ p ∈ S, p : ℕ) / B ≤ δ then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, if (∏ p ∈ S, p : ℕ) ≤ Real.exp (δ * B) then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0 := by
    apply sum_congr rfl
    intro S hS
    have hpos : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_powerset.mp hS hp)).pos)
    simp only [div_le_iff₀ hB0, Real.log_le_iff_le_exp hpos]
  have hloginv : Real.log (auxiliaryCutoff B) / (B : ℝ) = 1 / auxiliaryRatio B := by
    have hR := auxiliaryRatio_mul_log hB
    have hR0 : auxiliaryRatio B ≠ 0 := (auxiliaryRatio_pos hB).ne'
    field_simp
    nlinarith [hR]
  have hlogX : Real.log X ≤ Real.log (auxiliaryCutoff B) + δ * B := by
    by_cases h : (auxiliaryCutoff B : ℝ) ≤ Real.exp (δ * B)
    · dsimp only [X]
      rw [max_eq_right h, Real.log_exp]
      linarith [Real.log_natCast_nonneg (auxiliaryCutoff B)]
    · dsimp only [X]
      rw [max_eq_left (le_of_not_ge h)]
      nlinarith
  have hratio : Real.log X / Real.log (auxiliaryUpper B) ≤ δ + 1 / auxiliaryRatio B := by
    rw [auxiliaryUpper, Real.log_exp, ← hloginv]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)).mpr
    have hNlog := Real.log_natCast_nonneg (auxiliaryCutoff B)
    have hcancel : (Real.log (auxiliaryCutoff B) / (B : ℝ)) * B = Real.log (auxiliaryCutoff B) :=
      div_mul_cancel₀ _ hB0.ne'
    nlinarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogY0 : 0 ≤ Real.log (auxiliaryUpper B) := by
    rw [auxiliaryUpper, Real.log_exp]
    positivity
  rw [hevent]
  exact hsmall.trans ((hnormalizer X (auxiliaryUpper B) z hX hXY hz hz1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hlogX0 hlogY0) hratio hz) hC.le))

end JointDickman

end OAI
