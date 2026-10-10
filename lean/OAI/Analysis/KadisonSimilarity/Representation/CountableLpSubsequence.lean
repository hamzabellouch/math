import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A common almost-everywhere subsequence for countably many L² columns.
The fast diagonal choice uses summable errors, so the same sequence works
for every column. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Countably many L² limits have one choice of indices with simultaneous
pointwise convergence almost everywhere. -/
theorem exists_countable_L2_ae_subsequence
    (f : ℕ → ℕ → Lp H 2 μ) (g : ℕ → Lp H 2 μ)
    (hf : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧
      ∀ᵐ a ∂μ, ∀ j, Tendsto (fun n => f (k n) j a) atTop (𝓝 (g j a)) := by
  have hex (n : ℕ) : ∃ k, n ≤ k ∧
      ∀ j ∈ Finset.range (n + 1), ‖f k j - g j‖ ≤ (1 / 2 : ℝ) ^ n := by
    have hall : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (n + 1),
        ‖f k j - g j‖ < (1 / 2 : ℝ) ^ n := by
      apply (eventually_all_finset (Finset.range (n + 1))).mpr
      intro j _
      exact (tendsto_iff_norm_sub_tendsto_zero.mp (hf j)).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨k, hkn, hk⟩ := ((eventually_ge_atTop n).and hall).exists
    exact ⟨k, hkn, fun j hj => (hk j hj).le⟩
  choose k hk hfast using hex
  have hnorm (j : ℕ) : Summable (fun n => ‖f (k n) j - g j‖) := by
    apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop j] with n hn
    simpa only [norm_norm] using hfast n j (Finset.mem_range.mpr (by omega))
  have hae (j : ℕ) : ∀ᵐ a ∂μ, Summable (fun n => ‖(f (k n) j - g j) a‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [← Lp.enorm_def] using
      (tsum_enorm_ne_top_iff_summable_norm.mpr (hnorm j))
  refine ⟨k, hk, ?_⟩
  have heq : ∀ᵐ a ∂μ, ∀ j n,
      (f (k n) j - g j) a = f (k n) j a - g j a :=
    eventually_countable_forall.mpr fun j => eventually_countable_forall.mpr fun n =>
      Lp.coeFn_sub (f (k n) j) (g j)
  filter_upwards [eventually_countable_forall.mpr hae, heq] with a ha heq
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [heq] using (ha j).tendsto_atTop_zero

end KadisonSimilarity

end

end OAI
