import OAI.Analysis.CircleDomains.Probability.PrincipalDensityStability

namespace OAI

/-! Uniform compact support turns bounded coefficient approximation into
strong L2 convergence. The bound retains the same coefficient radius. -/
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma compact_coefficient_memLp {μ : ℂ → ℂ} {K : Set ℂ} {k : ℝ}
    (hm : AEStronglyMeasurable μ volume) (hK : IsCompact K)
    (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (hs : ∀ z ∉ K, μ z = 0) :
    MemLp μ 2 volume := by
  have hB : MemLp (K.indicator (fun _ : ℂ => (k : ℂ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  apply hB.of_le hm
  filter_upwards [] with z
  by_cases hz : z ∈ K
  · simpa only [indicator_of_mem hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hk] using hb z
  · simp only [hs z hz, norm_zero, indicator_of_notMem hz, le_refl]

lemma compact_coefficient_L2_convergence {μ : ℂ → ℂ} {ν : ℕ → ℂ → ℂ}
    {K : Set ℂ} {k : ℝ}
    (hm : AEStronglyMeasurable μ volume)
    (hn : ∀ n, AEStronglyMeasurable (ν n) volume)
    (hK : IsCompact K) (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (hc : ∀ n z, ‖ν n z‖ ≤ k)
    (hs : ∀ z ∉ K, μ z = 0) (ht : ∀ n z, z ∉ K → ν n z = 0)
    (hl : ∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) :
    Tendsto (fun n => (compact_coefficient_memLp (hn n) hK hk (hc n) (ht n)).toLp (ν n))
      atTop (𝓝 ((compact_coefficient_memLp hm hK hk hb hs).toLp μ)) := by
  let hμ := compact_coefficient_memLp hm hK hk hb hs
  let hν := fun n => compact_coefficient_memLp (hn n) hK hk (hc n) (ht n)
  have hB : MemLp (K.indicator (fun _ : ℂ => ((2*k : ℝ) : ℂ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  have hdom : ∀ n, ∀ᵐ z ∂volume,
      ‖(ν n - μ) z‖ ≤ ‖K.indicator (fun _ : ℂ => ((2*k : ℝ) : ℂ)) z‖ := by
    intro n
    filter_upwards [] with z
    by_cases hz : z ∈ K
    · simp only [Pi.sub_apply, indicator_of_mem hz, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 2*k by linarith)]
      exact (norm_sub_le _ _).trans (by linarith [hc n z, hb z])
    · simp only [Pi.sub_apply, hs z hz, ht n z hz, sub_self, norm_zero,
        indicator_of_notMem hz, le_refl]
  have hzero := dominated_toLp_zero_filter (fun n => (hν n).sub hμ) hB hdom
    (hl.mono (fun z hz => by simpa only [Pi.sub_apply, sub_self] using hz.sub_const (μ z)))
  change Tendsto (fun n => (hν n).toLp (ν n) - hμ.toLp μ) atTop (𝓝 0) at hzero
  simpa only [zero_add, sub_add_cancel] using hzero.add_const (hμ.toLp μ)

end CircleDomainRigidity

end

end OAI
