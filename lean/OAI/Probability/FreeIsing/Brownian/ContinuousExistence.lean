import OAI.Probability.FreeIsing.Brownian.DenseModification
import OAI.Probability.FreeIsing.Brownian.DyadicMoments
import OAI.Probability.FreeIsing.Brownian.Existence
import OAI.Probability.FreeIsing.Estimates.DyadicContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.BrownianContinuousExistence
open ContinuousModification BrownianDyadicMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def version (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => B (Real.toNNReal (dyadicLeft t n)) ω)

lemma toNNReal_nat_grid (n k : ℕ) :
    Real.toNNReal ((k : ℝ) / (2 : ℝ) ^ n) = time n k := by
  apply NNReal.coe_injective
  simp [time, Real.toNNReal_of_nonneg (by positivity : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n)]

lemma ae_continuous_version (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Continuous (fun t => version B t ω) := by
  filter_upwards [ae_eventually_increments hB] with ω hω
  apply DyadicContinuity.continuous_nnreal_dyadicLimit_of_nat_grid
    (fun t : ℝ => B t.toNNReal ω) (C := 1) (r := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  intro H
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω H)
  refine ⟨N, fun n hn k hk => ?_⟩
  have hh := hN n hn k hk
  rw [show ((k : ℝ) + 1) / 2 ^ n = ((k + 1 : ℕ) : ℝ) / 2 ^ n by push_cast; rfl,
    toNNReal_nat_grid, toNNReal_nat_grid]
  simpa only [Real.dist_eq, abs_sub_comm, one_mul] using hh

omit [MeasurableSpace Ω] in
lemma version_grid (B : ℝ≥0 → Ω → ℝ) (k : ℤ) (hk : 0 ≤ k) (n : ℕ) (ω : Ω) :
    version B (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω =
      B (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω := by
  have hg : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n := div_nonneg (by exact_mod_cast hk) (by positivity)
  unfold version
  rw [Real.coe_toNNReal _ hg]
  exact DyadicContinuity.dyadicLimit_grid (fun t : ℝ => B t.toNNReal ω) k n

theorem ae_eq_version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    B t =ᵐ[μ] version B t := by
  let s : ℕ → ℝ≥0 := fun n => (dyadicLeft t n).toNNReal
  have hs : Tendsto s atTop (𝓝 t) := by
    have hh := continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_dyadicLeft (t : ℝ))
    simpa only [Real.toNNReal_coe, Function.comp_def, s] using hh
  apply preBrownian_ae_eq_of_approximating_sequence hB (ae_continuous_version hB) hs
  intro n
  apply Filter.Eventually.of_forall
  intro ω
  exact (version_grid B ⌊(2 : ℝ) ^ n * (t : ℝ)⌋
    (Int.floor_nonneg.mpr (mul_nonneg (by positivity) t.property)) n ω).symm

theorem isBrownianReal_version (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (version B) μ :=
  ⟨hB.congr (ae_eq_version hB), ae_continuous_version hB⟩

theorem exists_brownianReal :
    ∃ (ν : Measure (ℝ≥0 → ℝ)) (B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
      IsProbabilityMeasure ν ∧ IsBrownianReal B ν :=
  ⟨BrownianExistence.preWienerMeasure, version (fun t ω => ω t), inferInstance,
    isBrownianReal_version BrownianExistence.coordinate_isPreBrownianReal⟩

end Problem367.BrownianContinuousExistence

end

end OAI
