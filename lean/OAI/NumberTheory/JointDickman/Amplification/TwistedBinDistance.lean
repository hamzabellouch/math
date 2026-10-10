import OAI.NumberTheory.JointDickman.Amplification.TwistedBinInterpolants
import OAI.NumberTheory.JointDickman.Counting.ComplexShortIntervalConsequences

namespace OAI

/-! # Uniform nonprincipal short averages for the bin interpolants -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem fixed_scale_small_power {J : ℕ} (hJ : 0 < J) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, (A*x)^(1/(2*(J : ℝ))) ≤ x^(1/(J : ℝ)) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop A] with x hx hAx
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ (x^2)^(1/(2*(J : ℝ))) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
    _ = x^(1/(J : ℝ)) := by
      rw [← Real.rpow_two,← Real.rpow_mul hx0]
      congr 1
      field_simp

theorem twistedWeightedBinInterpolant_distance
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A : ℝ} (hA : 0 < A) (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => minimumDistance
      (twistedWeightedBinInterpolant (fun i => primeBin (scale n) J (k i))
        (finitePrimeWeight P t) a χ) (A*scale n)) atTop atTop := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc1 : 1/(2*(J : ℝ)) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    apply (div_le_one (by positivity : (0 : ℝ) < 2*(J : ℝ))).mpr
    linarith
  have hnorm (n v : ℕ) :
      ‖twistedWeightedBinInterpolant (fun i => primeBin (scale n) J (k i))
        (finitePrimeWeight P t) a χ v‖ ≤ 1 := by
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ v
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds ht v).1]
    exact (finitePrimeWeight_bounds ht v).2
  apply minimumDistance_tendsto_of_prime_agreement hKMT hM χ hχ
    (by positivity : 0 < 1/(2*(J : ℝ))) hc1 P _ hnorm _ (hscale.const_mul_atTop hA)
  filter_upwards [hscale.eventually (fixed_scale_small_power hJ hA),
    hscale.eventually_ge_atTop 1] with n hpow h1
  intro p hp hpP hpX
  exact twistedWeightedBinInterpolant_small_prime hJ k hk hP t a χ h1 hp hpP (hpX.trans hpow)

theorem twistedWeightedBinInterpolant_short_averages
    (hMRT : ComplexShortIntervalInput) (hKMT : CharacterDistanceDivergence)
    (hM : PrimeReciprocalMertensInput)
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime) (t : ℕ → ℕ → ℝ)
    (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖complexShortAverage
          (twistedWeightedBinInterpolant (fun i => primeBin (scale n) J (k i))
            (finitePrimeWeight (P B) (t B)) a χ) (H B) z‖^2) < ε := by
  apply complexShortAverage_eventually_eventually hMRT
  · intro B n
    exact twistedWeightedBinInterpolant_multiplicative _ _
      (finitePrimeWeight_multiplicative (hP B) (t B)) a χ
  · intro B n v
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ v
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds (ht B) v).1]
    exact (finitePrimeWeight_bounds (ht B) v).2
  · exact hH
  · intro B
    exact hscale.const_mul_atTop (hA B)
  · intro B
    exact twistedWeightedBinInterpolant_distance hKMT hM hJ k hk (hP B) (t B)
      (ht B) a χ hχ (hA B) scale hscale

end JointDickman

end OAI
