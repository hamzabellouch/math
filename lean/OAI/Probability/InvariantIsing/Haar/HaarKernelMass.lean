import OAI.Probability.InvariantIsing.Haar.HaarKernelConvolution

namespace OAI

/-! Quantitative concentration of the positive polynomial kernels near the identity. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

lemma haarKernelMass_lower {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    μ.real {V | b < haarKernelBase 1 V} * b^n ≤ haarKernelMass μ n := by
  let S : Set (SpecialOrthogonal N) := {V | b < haarKernelBase 1 V}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (continuous_haarKernelBase 1).measurable
  have hi : Integrable (S.indicator (fun _ => b^n)) μ := (integrable_const _).indicator hS
  have hk := continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n)
  have hle : (∫ V, S.indicator (fun _ => b^n) V ∂μ) ≤ haarKernelMass μ n := by
    apply integral_mono hi hk
    intro V
    by_cases hV : V ∈ S
    · rw [Set.indicator_of_mem hV]
      exact pow_le_pow_left₀ hb hV.le n
    · rw [Set.indicator_of_notMem hV]
      exact pow_nonneg (haarKernelBase_nonneg 1 V) n
  simpa only [integral_indicator_const _ hS,smul_eq_mul] using hle

lemma haarKernel_superlevel_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] {b : ℝ} (hb : b < 2*N) :
    0 < μ.real {V | b < haarKernelBase 1 V} := by
  have hm : 0 < μ {V | b < haarKernelBase 1 V} := IsOpen.measure_pos μ
    (isOpen_lt continuous_const (continuous_haarKernelBase 1))
    ⟨1,by simpa only [mem_ofPred_eq,haarKernelBase_self] using hb⟩
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top μ _)

theorem haarKernelMass_ratio_tendsto_zero {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a : ℝ) (ha : 0 ≤ a) (haN : a < 2*N) :
    Tendsto (fun n : ℕ => a^n/haarKernelMass μ n) atTop (𝓝 0) := by
  let b := (a+2*N)/2
  have hab : a < b := by dsimp [b]; linarith
  have hbN : b < 2*N := by dsimp [b]; linarith
  have hb : 0 < b := ha.trans_lt hab
  let m := μ.real {V | b < haarKernelBase 1 V}
  have hm : 0 < m := haarKernel_superlevel_pos μ hbN
  have hr : a/b < 1 := (div_lt_one hb).mpr hab
  have hlim : Tendsto (fun n : ℕ => (a/b)^n/m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le) hr).div_const m
  apply squeeze_zero (fun n => div_nonneg (pow_nonneg ha n) (haarKernelMass_pos hN μ n).le) _ hlim
  intro n
  have hl := haarKernelMass_lower μ b hb.le n
  have hZ := haarKernelMass_pos hN μ n
  have hp := pow_pos hb n
  rw [div_pow]
  apply (div_le_div_iff₀ hZ hm).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  calc
    (a^n*m)*b^n = a^n*(m*b^n) := by ring
    _ ≤ a^n*haarKernelMass μ n := mul_le_mul_of_nonneg_left hl (pow_nonneg ha n)

end InvariantIsing

end

end OAI
