import OAI.NumberTheory.JointDickman.Amplification.TwistedBinDistance
import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceFilter
import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceDivergence
import OAI.NumberTheory.JointDickman.Amplification.HalaszRealCutoff

namespace OAI

/-! # Unconditional ordinary means for nonprincipal bin interpolants -/
namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem twistedWeightedBinInterpolant_distance_filter
    {κ : Type*} (l : Filter κ)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A : ℝ} (hA : 0 < A) (scale : κ → ℝ) (hscale : Tendsto scale l atTop) :
    Tendsto (fun n => minimumDistance
      (twistedWeightedBinInterpolant (fun i => primeBin (scale n) J (k i))
        (finitePrimeWeight P t) a χ) (A*scale n)) l atTop := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc1 : 1/(2*(J : ℝ)) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    apply (div_le_one (by positivity : (0 : ℝ) < 2*(J : ℝ))).mpr
    linarith
  have hnorm (n : κ) (v : ℕ) :
      ‖twistedWeightedBinInterpolant (fun i => primeBin (scale n) J (k i))
        (finitePrimeWeight P t) a χ v‖ ≤ 1 := by
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ v
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds ht v).1]
    exact (finitePrimeWeight_bounds ht v).2
  apply minimumDistance_tendsto_of_prime_agreement_filter l hKMT hM χ hχ
    (by positivity : 0 < 1/(2*(J : ℝ))) hc1 P _ hnorm _ (hscale.const_mul_atTop hA)
  filter_upwards [hscale.eventually (fixed_scale_small_power hJ hA),
    hscale.eventually_ge_atTop 1] with n hpow h1
  intro p hp hpP hpX
  exact twistedWeightedBinInterpolant_small_prime hJ k hk hP t a χ h1 hp hpP (hpX.trans hpow)

theorem twistedWeightedBinInterpolant_prefix_mean
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
        twistedWeightedBinInterpolant (fun i => primeBin x J (k i))
          (finitePrimeWeight P t) a χ n) / (A*x : ℂ)) atTop (𝓝 0) := by
  simp only [←Complex.ofReal_mul]
  apply halasz_real_mean_tendsto_zero atTop (fun x : ℝ => A*x)
    (tendsto_id.const_mul_atTop hA)
    (fun x => twistedWeightedBinInterpolant (fun i => primeBin x J (k i))
      (finitePrimeWeight P t) a χ)
  · intro x
    exact twistedWeightedBinInterpolant_multiplicative _ _
      (finitePrimeWeight_multiplicative hP t) a χ
  · intro x n
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ n
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds ht v).1]
    exact (finitePrimeWeight_bounds ht v).2
  · exact twistedWeightedBinInterpolant_distance_filter atTop characterDistanceDivergence
      primeReciprocalMertensInput hJ k hk hP t ht a χ hχ hA id tendsto_id

end JointDickman

end OAI
