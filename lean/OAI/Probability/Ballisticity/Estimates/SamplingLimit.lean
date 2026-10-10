import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.Sampling

variable {X : Type*} [MeasurableSpace X]

theorem ae_tendsto_zero_of_sq_integrals {μ : Measure X} (f : ℕ → X → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal ((f n x)^2) ∂μ ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  have hm (n) : AEMeasurable (fun x => ENNReal.ofReal ((f n x)^2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hf n).aemeasurable.pow_const 2)
  have hfin : (∫⁻ x, ∑' n, ENNReal.ofReal ((f n x)^2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    exact (ENNReal.tsum_le_tsum hbound).trans_lt hb.tsum_ofReal_lt_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with x hx
  have hs := ENNReal.summable_toReal hx.ne
  have he : (fun n => (ENNReal.ofReal ((f n x)^2)).toReal) = (fun n => (f n x)^2) := by
    funext n
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  rw [he] at hs
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

section Compact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

lemma sq_integral_bound_of_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : C(X,ℝ)) {b : ℝ}
    (hb : ∀ k, ∫ x, (f x)^2 ∂(μs k : Measure X) ≤ b) :
    ∫ x, (f x)^2 ∂μ ≤ b := by
  let g : C(X,ℝ) := ⟨fun x => (f x)^2, f.continuous.pow 2⟩
  have ht := (ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp hμ
  exact le_of_tendsto ht (Eventually.of_forall hb)

theorem ae_sampling_of_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (e : ℕ → C(X,ℝ)) (b : ℕ → ℝ) (hb : Summable b)
    (he : ∀ k n, ∫ x, (e n x)^2 ∂(μs k : Measure X) ≤ b n) :
    ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => e n x) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_sq_integrals (fun n => e n) (fun n => (e n).continuous.aestronglyMeasurable) b hb
  intro n
  have hi : Integrable (fun x => (e n x)^2) (μ : Measure X) :=
    ((e n).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (sq_integral_bound_of_weak_limit μs μ hμ (e n) (fun k => he k n))

end Compact
end DirectionalTransience.Sampling

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.Sampling

variable {X : Type*} [MeasurableSpace X]

lemma cutoff_tendsto (w : ℝ) (hw : 0 ≤ w) :
    Tendsto (fun n : ℕ => max 0 (1-(n:ℝ)*w)) atTop (𝓝 (if w=0 then 1 else 0)) := by
  by_cases h : w=0
  · simp [h]
  · rw [ite_eq_right h]
    have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm h)
    obtain ⟨N,hN⟩ := exists_nat_gt (1/w)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hnw : 1 < (n:ℝ)*w := (div_lt_iff₀ hp).mp (hN.trans_le hn')
    exact (max_eq_left (by linarith)).symm

theorem ae_zero_of_sampling_tests {μ : Measure X} [IsFiniteMeasure μ]
    (w I : X → ℝ) (hw : Measurable w) (hI : Measurable I)
    (hw01 : ∀ x, w x ∈ Set.Icc (0:ℝ) 1)
    (hI01 : ∀ x, I x ∈ Set.Icc (0:ℝ) 1)
    (htest : ∀ g : C(ℝ,ℝ), (∫ x, g (w x)*(I x-w x) ∂μ)=0) :
    ∀ᵐ x ∂μ, w x=0 → I x=0 := by
  classical
  let F : ℕ → X → ℝ := fun n x => max 0 (1-(n:ℝ)*w x)*(I x-w x)
  let G : X → ℝ := fun x => if w x=0 then I x else 0
  have hFm (n : ℕ) : Measurable (F n) := by dsimp [F]; fun_prop
  have hGm : Measurable G := by
    dsimp [G]
    exact Measurable.ite (hw (measurableSet_singleton 0)) hI measurable_const
  have hgb x : 0 ≤ G x ∧ G x ≤ 1 := by
    dsimp [G]
    split_ifs
    · exact hI01 x
    · norm_num
  have hFb (n : ℕ) (x : X) : ‖F n x‖ ≤ 1 := by
    have hc0 : 0 ≤ max 0 (1-(n:ℝ)*w x) := le_max_left _ _
    have hc1 : max 0 (1-(n:ℝ)*w x) ≤ 1 := by
      apply max_le (by norm_num)
      have hh := mul_nonneg (Nat.cast_nonneg n) (hw01 x).1
      linarith
    have hsub : |I x-w x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hI01 x).1,(hI01 x).2,(hw01 x).1,(hw01 x).2]
    dsimp [F]
    rw [abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hsub hc0).trans (by simpa using hc1)
  have hFlim (x : X) : Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    have hh := (cutoff_tendsto (w x) (hw01 x).1).mul_const (I x-w x)
    convert hh using 1
    dsimp [G]
    split_ifs with h <;> simp [h]
  have hi := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1:ℝ))
    (fun n => (hFm n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (hFb n)) (Eventually.of_forall hFlim)
  have hFzero (n : ℕ) : (∫ x, F n x ∂μ)=0 := by
    exact htest ⟨fun t => max 0 (1-(n:ℝ)*t),by fun_prop⟩
  simp only [hFzero] at hi
  have hGzero : (∫ x, G x ∂μ)=0 := tendsto_nhds_unique hi tendsto_const_nhds
  have hGi : Integrable G μ := (integrable_const (1:ℝ)).mono' hGm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => (hgb x).1) hGi).mp hGzero
  filter_upwards [hz] with x hx h
  simpa [G,h] using hx

section Compact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem sampling_tests_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (w I : C(X,ℝ))
    (htest : ∀ k (g : C(ℝ,ℝ)),
      (∫ x, g (w x)*(I x-w x) ∂(μs k : Measure X))=0) :
    ∀ g : C(ℝ,ℝ), (∫ x, g (w x)*(I x-w x) ∂(μ : Measure X))=0 := by
  intro g
  let F : C(X,ℝ) := ⟨fun x => g (w x)*(I x-w x),by fun_prop⟩
  have ht := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hμ
  have he (k) : (∫ x, F x ∂(μs k : Measure X))=0 := htest k g
  change Tendsto (fun k => ∫ x, F x ∂(μs k : Measure X)) atTop _ at ht
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end Compact
end DirectionalTransience.Sampling

end

end OAI
