import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHeightWeight

namespace OAI

/-! # A whole-line weighted moment from compact height moments -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

noncomputable def densityShellBudget (A : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => A
  | j + 1 => 2 * A * ((j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j)

 theorem densityShellBudget_nonneg (A : ℝ) (hA : 0 ≤ A) (k j : ℕ) :
    0 ≤ densityShellBudget A k j := by
  cases j <;> simp only [densityShellBudget] <;> positivity

 theorem densityShellBudget_summable (A : ℝ) (k : ℕ) : Summable (densityShellBudget A k) := by
  apply (summable_nat_add_iff 1).mp
  exact (density_height_energy_summable k).mul_left (2 * A)

 theorem densityShellBudget_sum (A : ℝ) (k : ℕ) :
    (∑' j, densityShellBudget A k j) = A * densityHeightEnergyConstant k := by
  rw [(densityShellBudget_summable A k).tsum_eq_zero_add]
  simp only [densityShellBudget]
  rw [tsum_mul_left]
  unfold densityHeightEnergyConstant
  ring

 theorem density_weighted_shell_bound (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (T : ℝ) (hT : 0 < T) (A : ℝ) (k : ℕ)
    (hball : ∀ j : ℕ, (∫ x in densityHeightBall T j, f x) ≤
      A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ k) (j : ℕ) :
    (∫ x in densityHeightShell T j, densityHeightWeight T x * f x) ≤
      densityShellBudget A k j := by
  have hi (j : ℕ) : IntegrableOn f (densityHeightBall T j) := hf.continuousOn.integrableOn_Icc
  have hiw (j : ℕ) : IntegrableOn (fun x => densityHeightWeight T x * f x) (densityHeightShell T j) :=
    (((densityHeightWeight_continuous T).mul hf).continuousOn.integrableOn_Icc).mono_set
      (densityHeightShell_subset T j)
  cases j with
  | zero =>
    apply (integral_mono (hiw 0) (hi 0) (fun x => ?_)).trans
    · simpa only [densityHeightShell, densityShellBudget, pow_zero, mul_one, Nat.cast_zero, zero_add, one_pow] using hball 0
    · exact mul_le_of_le_one_left (hf0 x) (densityCubicWeight_le_one _)
  | succ j =>
    have hsub : (∫ x in densityHeightShell T (j + 1), f x) ≤
        ∫ x in densityHeightBall T (j + 1), f x :=
      setIntegral_mono_set (hi (j + 1)) (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall (fun _ hx => densityHeightShell_subset T (j + 1) hx))
    calc
      _ ≤ (1 / 8 : ℝ) ^ j * ∫ x in densityHeightShell T (j + 1), f x := by
        rw [← integral_const_mul]
        apply setIntegral_mono_on (hiw (j + 1))
          (((hi (j + 1)).mono_set (densityHeightShell_subset T (j + 1))).const_mul _)
          (densityHeightShell_measurable T (j + 1))
        intro x hx
        exact mul_le_mul_of_nonneg_right (densityHeightWeight_shell T hT j x hx) (hf0 x)
      _ ≤ (1 / 8 : ℝ) ^ j * (A * (2 : ℝ) ^ (j + 1) * (j + 1 + 1 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hsub.trans (by
          simpa only [Nat.cast_add, Nat.cast_one] using hball (j + 1))) (by positivity)
      _ = densityShellBudget A k (j + 1) := by
        simp only [densityShellBudget, pow_succ]
        have he : (1 / 8 : ℝ) ^ j * (2 : ℝ) ^ j = (1 / 4 : ℝ) ^ j := by
          rw [← mul_pow]
          norm_num
        rw [show (j + 1 + 1 : ℝ) = j + 2 by ring]
        calc
          _ = 2 * A * (j + 2 : ℝ) ^ k * ((1 / 8 : ℝ) ^ j * (2 : ℝ) ^ j) := by ring
          _ = _ := by rw [he]; ring

 theorem density_weighted_moment (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (T : ℝ) (hT : 0 < T) (A : ℝ) (_hA : 0 ≤ A) (k : ℕ)
    (hball : ∀ j : ℕ, (∫ x in densityHeightBall T j, f x) ≤
      A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ k) :
    Integrable (fun x => densityHeightWeight T x * f x) ∧
      (∫ x, densityHeightWeight T x * f x) ≤ A * densityHeightEnergyConstant k := by
  let g := fun x => densityHeightWeight T x * f x
  have hg0 (x : ℝ) : 0 ≤ g x := mul_nonneg (densityHeightWeight_nonneg T x) (hf0 x)
  have hi (j : ℕ) : IntegrableOn g (densityHeightShell T j) :=
    (((densityHeightWeight_continuous T).mul hf).continuousOn.integrableOn_Icc).mono_set
      (densityHeightShell_subset T j)
  have hb (j : ℕ) : (∫ x in densityHeightShell T j, g x) ≤ densityShellBudget A k j :=
    density_weighted_shell_bound f hf hf0 T hT A k hball j
  have hsum : Summable (fun j => ∫ x in densityHeightShell T j, g x) :=
    (densityShellBudget_summable A k).of_nonneg_of_le
      (fun j => integral_nonneg (fun x => hg0 x)) hb
  have hnorm : Summable (fun j => ∫ x in densityHeightShell T j, ‖g x‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hsum
  have hgi := integrableOn_iUnion_of_summable_integral_norm hi hnorm
  rw [densityHeightShell_cover T hT, integrableOn_univ] at hgi
  refine ⟨hgi, ?_⟩
  have he := integral_iUnion (densityHeightShell_measurable T)
    (densityHeightShell_disjoint T hT.le) (show IntegrableOn g (⋃ j, densityHeightShell T j) by
      rwa [densityHeightShell_cover T hT, integrableOn_univ])
  rw [densityHeightShell_cover T hT, setIntegral_univ] at he
  change (∫ x, g x) ≤ _
  rw [he, ← densityShellBudget_sum A k]
  exact hsum.tsum_le_tsum hb (densityShellBudget_summable A k)

end Ostmann

end OAI
