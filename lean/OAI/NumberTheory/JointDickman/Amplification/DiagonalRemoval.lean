import OAI.NumberTheory.JointDickman.Amplification.FirstFormMass
import OAI.NumberTheory.JointDickman.Amplification.AmplificationMultiplier

namespace OAI

/-! # The actual smooth amplification has a negligible diagonal -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationOuterWeight (B c : ℕ) : ℝ :=
  amplificationBump (Real.log c / B)

noncomputable def amplificationInnerWeight (T a c : ℕ) : ℝ :=
  amplificationBump ((a : ℝ) / ((T : ℝ)*c))

theorem firstFormDiagonal_arithmetic_le {B : ℕ} (hB : 0 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (Q : ℝ)
    (hu : ∀ c, 0 ≤ u c) (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖ ≤ 2)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q) :
    firstFormDiagonal B L τ C u v J N ≤ 4*Q*(B : ℝ)*
      ((∑ n ∈ range N, arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n)/(N : ℝ)) := by
  have h := firstFormDiagonal_le B L τ C u v J (fun _ => 1) N Q hu hv
    (fun n => by nlinarith [norm_nonneg (J n), hJ n]) hcap
  rw [firstFormMass_reindex hB] at h
  simpa only [one_mul, mul_assoc] using h

/-- The limits are taken in the manuscript's order: first the counting
scale N, then B. This statement is uniform over all bounded second labels. -/
theorem smooth_diagonal_negligible
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau)
    (C : ℝ) (J : ℕ → ℕ → ℂ) (hJ : ∀ N n, ‖J N n‖ ≤ 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      firstFormDiagonal B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J N) N /
        ((B : ℝ)*amplificationMultiplier B) ≤ ε := by
  obtain ⟨Q,hQlim,hQbound⟩ := regular_pair_cap_negligible hL hτ hτsmall
  obtain ⟨K,hK,hKbound⟩ := smooth_arithmetic_first_upper hFord hM L τ C
  intro ε hε
  have hlim := hQlim.const_mul (4*(K+1))
  simp only [mul_zero] at hlim
  have hsmall := hlim.eventually (eventually_le_nhds hε)
  filter_upwards [hQbound,hKbound,amplificationMultiplier_valid,hsmall,eventually_gt_atTop 0]
    with B hcap hmoment hT hsmallB hB
  have hBT : (0 : ℝ) < (B : ℝ)*amplificationMultiplier B :=
    mul_pos (by exact_mod_cast hB) (by exact_mod_cast hT.1)
  have hm := hmoment (amplificationMultiplier B) hT.1 hT.2
  have hmean := arithmeticAmplification_moment_tendsto B L τ C
    (amplificationSmoothWeight B (amplificationMultiplier B)) 1
  have havg : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, arithmeticSubsetAmplification B L τ C
        (amplificationSmoothWeight B (amplificationMultiplier B)) n)/(N : ℝ) ≤ K+1 := by
    simpa only [pow_one] using hmean.eventually
      (eventually_le_nhds (lt_of_le_of_lt hm (by linarith)))
  filter_upwards [havg] with N havgN
  have hQ0 : 0 ≤ Q B := (mul_nonneg (regularCoefficientWeight_nonneg B L τ C 0)
    (regularResidueWeight_nonneg B L τ C ∅)).trans (hcap C 0 ∅)
  have hd := firstFormDiagonal_arithmetic_le hB L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight (amplificationMultiplier B))
    (J N) N (Q B) (fun c => (amplificationBump_bounds _).1)
    (fun a c => amplificationBump_bounds _) (hJ N)
    (fun a m => hcap C a (coefficientPrimeSet B m))
  have hratio : 0 ≤ Q B / (amplificationMultiplier B : ℝ) := div_nonneg hQ0 (Nat.cast_nonneg _)
  have hquot := div_le_div_of_nonneg_right hd hBT.le
  have he (A : ℝ) : (4*Q B*(B : ℝ)*A)/((B : ℝ)*amplificationMultiplier B) =
      4*(Q B/(amplificationMultiplier B : ℝ))*A := by
    have hb0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
    have ht0 : (amplificationMultiplier B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT.1)
    field_simp
  rw [he] at hquot
  have heq : (fun a c => amplificationOuterWeight B c *
      amplificationInnerWeight (amplificationMultiplier B) a c) =
      amplificationSmoothWeight B (amplificationMultiplier B) := rfl
  rw [heq] at hquot
  calc
    _ ≤ _ := hquot
    _ ≤ 4*(Q B/(amplificationMultiplier B : ℝ))*(K+1) :=
      mul_le_mul_of_nonneg_left havgN (mul_nonneg (by norm_num) hratio)
    _ ≤ ε := by nlinarith [hsmallB]

end JointDickman

end OAI
