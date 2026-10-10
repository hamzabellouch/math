import OAI.NumberTheory.JointDickman.Analysis.ShortMellinDyadicEnergy
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # The qualitative short-interval consequence of a vanishing spectral budget -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

lemma exists_mellin_smoothing_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ m : ℕ, 0 < m ∧
      2 * (3 / (m : ℝ) + 16 * η) ^ 2 < ε := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hden
  have ht : Tendsto (fun n : ℕ => 2 * (19 / ((n : ℝ) + 3)) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hi.const_mul 19).pow 2).const_mul 2
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨1 / ((n : ℝ) + 3), by positivity, ?_, n + 3, by omega, ?_⟩
  · apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 3) (by norm_num : (0 : ℝ) < 2)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · convert hn using 1
    push_cast
    ring

/-- This purely analytic implication applies also to the iterated scale
filter. Its premise is the literal finite Dirichlet-polynomial estimate. -/
theorem shortAverage_tendsto_zero_of_mellin_bound {ι : Type*} (l : Filter ι)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i n, ‖f i n‖ ≤ 1)
    (H X A B : ι → ℝ) (hH : Tendsto H l atTop) (hX : Tendsto X l atTop)
    (hHX : Tendsto (fun i => H i / X i) l (𝓝 0))
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbudget : Tendsto (fun i => A i + B i * X i / H i) l (𝓝 0))
    (hspectral : ∀ᶠ i in l, ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X i⌋₊ ⌊4 * X i⌋₊) (f i) t‖ ^ 2) ≤
        A i + B i * T) :
    Tendsto (fun i => (1 / X i) * (∫ x in X i..2 * X i,
      ‖complexShortAverage (f i) (H i) x‖ ^ 2)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηhalf, m, hm, hsmall⟩ :=
    exists_mellin_smoothing_parameters (show 0 < ε / 2 by positivity)
  obtain ⟨C, hC, hbound⟩ := shortAverage_dyadic_energy η hη hηhalf m hm
  have hinvH := tendsto_inv_atTop_zero.comp hH
  have hinvX := tendsto_inv_atTop_zero.comp hX
  have he : Tendsto (fun i => 2 *
      (3 / (m : ℝ) + 11 / H i + H i / X i + 1 / X i + 16 * η) ^ 2)
      l (𝓝 (2 * (3 / (m : ℝ) + 16 * η) ^ 2)) := by
    have ht := (((((tendsto_const_nhds (x := 3 / (m : ℝ))).add
      (hinvH.const_mul 11)).add hHX).add hinvX).add
        (tendsto_const_nhds (x := 16 * η))).pow 2
    simpa only [Function.comp_apply, div_eq_mul_inv, one_mul, mul_zero, add_zero] using ht.const_mul 2
  have hevent := he.eventually (gt_mem_nhds hsmall)
  have hbevent := (hbudget.const_mul C).eventually
    (gt_mem_nhds (show C * 0 < ε / 2 by simpa using (show 0 < ε / 2 by positivity)))
  have hratio := hHX.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hspectral, hevent, hbevent, hratio,
    hH.eventually_ge_atTop 1, hX.eventually_gt_atTop 0] with i hspec herr hbud hrat hHi hXi
  have hHXi : H i ≤ X i := (div_le_one hXi).mp hrat.le
  have hb := hbound (f i) (hf i) (X i) (H i) hXi hHi hHXi (A i) (B i) (hA i) (hB i) hspec
  have hnonneg : 0 ≤ (1 / X i) * (∫ x in X i..2 * X i,
      ‖complexShortAverage (f i) (H i) x‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

end JointDickman

end OAI
