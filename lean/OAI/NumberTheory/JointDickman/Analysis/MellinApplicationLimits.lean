import OAI.NumberTheory.JointDickman.Analysis.MellinShortLimit
import OAI.NumberTheory.JointDickman.Analysis.CenteredMellinEnergy
import OAI.NumberTheory.JointDickman.Counting.TypicalShortEnergy

namespace OAI

/-! # Analytic limit transfers for the two required short-interval applications -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

private lemma eventually_short_scales {ι : Type*} {l : Filter ι} {H X : ι → ℝ}
    (hH : Tendsto H l atTop) (hX : Tendsto X l atTop)
    (hHX : Tendsto (fun i => H i / X i) l (𝓝 0)) :
    ∀ᶠ i in l, 0 < X i ∧ 1 ≤ H i ∧ H i ≤ X i := by
  filter_upwards [hH.eventually_ge_atTop 1, hX.eventually_gt_atTop 0,
    hHX.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hHi hXi hratio
  exact ⟨hXi, hHi, (div_le_one hXi).mp hratio.le⟩

private lemma eventually_short_energy_nonneg {ι : Type*} {l : Filter ι}
    (f : ι → ArithmeticFunction ℂ) (H X : ι → ℝ) (c : ι → ℂ)
    (hX : Tendsto X l atTop) :
    ∀ᶠ i in l, 0 ≤ (1 / X i) * (∫ x in X i..2 * X i,
      ‖complexShortAverage (f i) (H i) x - c i‖ ^ 2) := by
  filter_upwards [hX.eventually_gt_atTop 0] with i hi
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

/-- The same spectral limit gives centered short means, including a
scale-dependent dyadic long mean of norm at most two. -/
theorem centeredShortAverage_tendsto_zero_of_mellin_bound {ι : Type*} (l : Filter ι)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i n, ‖f i n‖ ≤ 1)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 2)
    (H X A B : ι → ℝ) (hH : Tendsto H l atTop) (hX : Tendsto X l atTop)
    (hHX : Tendsto (fun i => H i / X i) l (𝓝 0))
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbudget : Tendsto (fun i => A i + B i * X i / H i) l (𝓝 0))
    (hspectral : ∀ᶠ i in l, ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X i⌋₊ ⌊4 * X i⌋₊)
        (centeredShortCoefficients (f i) (c i)) t‖ ^ 2) ≤ A i + B i * T) :
    Tendsto (fun i => (1 / X i) * (∫ x in X i..2 * X i,
      ‖complexShortAverage (f i) (H i) x - c i‖ ^ 2)) l (𝓝 0) := by
  have hg := shortAverage_tendsto_zero_of_mellin_bound l
    (fun i => centeredShortCoefficients (f i) (c i))
    (fun i => centeredShortCoefficients_norm_le (f i) (hf i) (hc i))
    H X A B hH hX hHX hA hB hbudget hspectral
  have hi : Tendsto (fun i => 8 / H i ^ 2) l (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero.comp hH).pow 2).const_mul 8
  have hupper : ∀ᶠ i in l,
      (1 / X i) * (∫ x in X i..2 * X i, ‖complexShortAverage (f i) (H i) x - c i‖ ^ 2) ≤
        18 * ((1 / X i) * (∫ x in X i..2 * X i,
          ‖complexShortAverage (centeredShortCoefficients (f i) (c i)) (H i) x‖ ^ 2)) + 8 / H i ^ 2 := by
    filter_upwards [eventually_short_scales hH hX hHX] with i hi
    exact centeredShort_energy_le (f i) (hf i) (hc i) hi.1 (by linarith [hi.2.1])
  apply squeeze_zero' (eventually_short_energy_nonneg f H X c hX) hupper
  simpa only [mul_zero, add_zero] using (hg.const_mul 18).add hi

/-- The typical-set sieve error is paid in ordinary counting density. -/
theorem shortAverage_tendsto_zero_of_typical_mellin_bound {ι : Type*} (l : Filter ι)
    (S : ι → ℕ → Prop) [∀ i, DecidablePred (S i)]
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i n, ‖f i n‖ ≤ 1)
    (H X A B : ι → ℝ) (hH : Tendsto H l atTop) (hX : Tendsto X l atTop)
    (hHX : Tendsto (fun i => H i / X i) l (𝓝 0))
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbudget : Tendsto (fun i => A i + B i * X i / H i) l (𝓝 0))
    (hspectral : ∀ᶠ i in l, ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X i⌋₊ ⌊4 * X i⌋₊)
        (restrictArithmetic (S i) (f i)) t‖ ^ 2) ≤ A i + B i * T)
    (hmissing : Tendsto (fun i =>
      (((range (⌊3 * X i⌋₊ + 1)).filter fun n => ¬S i n).card : ℝ) / X i) l (𝓝 0)) :
    Tendsto (fun i => (1 / X i) * (∫ x in X i..2 * X i,
      ‖complexShortAverage (f i) (H i) x‖ ^ 2)) l (𝓝 0) := by
  have hg := shortAverage_tendsto_zero_of_mellin_bound l
    (fun i => restrictArithmetic (S i) (f i))
    (fun i => restrictArithmetic_norm_le (S i) (f i) (hf i))
    H X A B hH hX hHX hA hB hbudget hspectral
  have hupper : ∀ᶠ i in l,
      (1 / X i) * (∫ x in X i..2 * X i, ‖complexShortAverage (f i) (H i) x‖ ^ 2) ≤
        2 * ((1 / X i) * (∫ x in X i..2 * X i,
          ‖complexShortAverage (restrictArithmetic (S i) (f i)) (H i) x‖ ^ 2)) +
          4 * ((((range (⌊3 * X i⌋₊ + 1)).filter fun n => ¬S i n).card : ℝ) / X i) := by
    filter_upwards [eventually_short_scales hH hX hHX] with i hi
    convert shortAverage_restrict_energy (S i) (f i) (hf i) hi.1 hi.2.1 hi.2.2 using 1
    ring
  have hnonneg := eventually_short_energy_nonneg f H X (fun _ => 0) hX
  simp only [sub_zero] at hnonneg
  apply squeeze_zero' hnonneg hupper
  simpa only [mul_zero, add_zero] using (hg.const_mul 2).add (hmissing.const_mul 4)

end JointDickman

end OAI
