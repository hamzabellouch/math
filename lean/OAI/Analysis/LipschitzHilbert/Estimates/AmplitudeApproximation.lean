import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongForm
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! The finite amplitude approximations converge in squared L2 energy.
The cutoff is the actual disjoint union of its amplitude levels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] in
theorem amplitude_scaled_piece (f : X → EuclideanSpace ℂ κ) (i : ℤ) :
    (2:ℝ)^i • amplitudePiece f i=(amplitudeLevel f i).indicator f := by
  funext x
  simp only [amplitudePiece,Pi.smul_apply,smul_smul]
  rw [←zpow_add₀ (by norm_num : (2:ℝ)≠0),add_neg_cancel,zpow_zero,one_smul]

omit [MeasurableSpace X] in
theorem amplitudeApprox_eq_indicator (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) :
    amplitudeApprox f I=(⋃ i∈I, amplitudeLevel f i).indicator f := by
  funext x
  simp only [amplitudeApprox,amplitude_scaled_piece,Finset.sum_apply]
  exact (Finset.indicator_biUnion_apply I (amplitudeLevel f)
    (fun i _ j _ hij => amplitudeLevel_disjoint f hij) x).symm

theorem amplitudeApprox_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (I : Finset ℤ) :
    Measurable (amplitudeApprox f I) := by
  rw [amplitudeApprox_eq_indicator]
  exact hf.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hf.norm i))

theorem amplitudeApprox_memLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (I : Finset ℤ) : MemLp (amplitudeApprox f I) 2 μ := by
  rw [amplitudeApprox_eq_indicator]
  exact hf2.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudeApprox_sub_norm_le (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) (x : X) :
    ‖amplitudeApprox f I x-f x‖≤‖f x‖ := by
  rw [amplitudeApprox_eq_indicator]
  by_cases hx : x∈⋃ i∈I, amplitudeLevel f i
  · simp only [Set.indicator_of_mem hx,sub_self,norm_zero,norm_nonneg]
  · simp only [Set.indicator_of_notMem hx,zero_sub,norm_neg,le_refl]

omit [MeasurableSpace X] in
theorem amplitudeApprox_eventually_eq (f : X → EuclideanSpace ℂ κ) (x : X) :
    ∀ᶠ n : ℕ in atTop, amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x=f x := by
  by_cases hx : f x=0
  · filter_upwards [] with n
    rw [amplitudeApprox_eq_indicator]
    by_cases hm : x∈⋃ i∈Finset.Icc (-(n:ℤ)) n, amplitudeLevel f i
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm,hx]
  · obtain ⟨i,hi⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx) (by norm_num : (1:ℝ)<2)
    have hlevel : x∈amplitudeLevel f (i+1) := by
      change (2:ℝ)^(i+1-1)<‖f x‖ ∧ ‖f x‖≤(2:ℝ)^(i+1)
      simpa only [Set.mem_Ioc,add_sub_cancel_right] using hi
    filter_upwards [eventually_ge_atTop (i+1).natAbs] with n hn
    rw [amplitudeApprox_eq_indicator,Set.indicator_of_mem]
    exact Set.mem_iUnion.mpr ⟨i+1,Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr (by omega),hlevel⟩⟩

theorem amplitudeApprox_energy_tendsto (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => ∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2 ∂μ)
      atTop (𝓝 0) := by
  have hdom := hf2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have h := tendsto_integral_of_dominated_convergence (μ:=μ) (fun x => ‖f x‖^2)
    (F:=fun n x => ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2) (f:=fun _ => (0:ℝ))
    (fun n => (((amplitudeApprox_measurable hf _).sub hf).norm.pow_const 2).aestronglyMeasurable)
    hdom
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (amplitudeApprox_sub_norm_le f _ x) 2))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [amplitudeApprox_eventually_eq f x] with n hn
      simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)]))
  simpa only [integral_zero] using h

theorem amplitudeApprox_Lp_tendsto (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => (amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)).toLp
      (amplitudeApprox f (Finset.Icc (-(n:ℤ)) n))) atTop (𝓝 (hf2.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => amplitudeApprox f (Finset.Icc (-(n:ℤ)) n))
    (fun n => amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)) f hf2).mpr
  have he (n : ℕ) : eLpNorm (amplitudeApprox f (Finset.Icc (-(n:ℤ)) n)-f) 2 μ=
      ENNReal.ofReal (Real.sqrt (∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2 ∂μ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)).sub hf2)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (amplitudeApprox_energy_tendsto μ hf hf2))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using h

end LipschitzHilbert

end

end OAI
