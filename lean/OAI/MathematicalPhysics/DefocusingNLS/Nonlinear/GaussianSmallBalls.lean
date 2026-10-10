import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianBlocks
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianMoments
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianSupport
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-!
# Small balls for square-summable Gaussian coefficients

The random tail has arbitrarily small expected energy; a finite head can be
placed near any prescribed target independently of that tail. The argument
proves the coefficient-space probability estimate used for Hilbert support.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DefocusingNLS

section CountableProduct

variable {ι : Type*} [Countable ι]

/-- Energy beyond a finite set of Fourier frequencies. -/
noncomputable def gaussianTailEnergy (w : ι → ℝ) (S : Finset ι) (g : ι → ℂ) : ℝ≥0∞ :=
  ∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (w i) * ENNReal.ofReal (Complex.normSq (g i))

theorem measurable_gaussianTailEnergy (w : ι → ℝ) (S : Finset ι) :
    Measurable (gaussianTailEnergy w S) := by
  apply Measurable.tsum
  intro i
  fun_prop

/-- The mean tail energy is exactly the sum of the tail variances. -/
theorem gaussianTailEnergy_mean (w : ι → ℝ) (S : Finset ι) :
    (∫⁻ g, gaussianTailEnergy w S g
      ∂Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))) =
    ∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (w i) := by
  unfold gaussianTailEnergy
  have hm : ∀ i : ↥((S : Set ι)ᶜ),
      Measurable (fun g : ι → ℂ =>
        ENNReal.ofReal (w i) * ENNReal.ofReal (Complex.normSq (g i))) := by
    intro i
    fun_prop
  rw [lintegral_tsum (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  rw [lintegral_const_mul _ (by fun_prop)]
  have hcoord : (∫⁻ g : ι → ℂ, ENNReal.ofReal (Complex.normSq (g i))
      ∂Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))) = 1 := by
    rw [← lintegral_map (f := fun z : ℂ => ENNReal.ofReal (Complex.normSq z))
      (g := fun g : ι → ℂ => g i) (by fun_prop) (by fun_prop), Measure.infinitePi_map_eval]
    exact standard_complex_gaussian_normSq_moment
  rw [hcoord, mul_one]

/-- A small expected tail produces a positive-probability small-tail event. -/
theorem gaussianTailEnergy_small_pos (w : ι → ℝ) (S : Finset ι) {c : ℝ≥0∞}
    (hmean : (∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (w i)) < c) :
    0 < Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))
      {g | gaussianTailEnergy w S g < c} := by
  apply positive_sublevel_of_lintegral_lt
  rwa [gaussianTailEnergy_mean]

omit [Countable ι] in
/-- One finite set makes both a summable variance tail and a square-summable
fixed target tail small. -/
theorem exists_small_variance_target_tails (w : ι → ℝ) (hw : Summable w)
    (f : ι → ℂ) (hf : Summable (fun i => ‖f i‖ ^ 2)) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ S : Finset ι,
      (∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (w i)) < c ∧
      (∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (‖f i‖ ^ 2)) < c := by
  have hwlim := ENNReal.tendsto_tsum_compl_atTop_zero hw.tsum_ofReal_ne_top
  have hflim := ENNReal.tendsto_tsum_compl_atTop_zero hf.tsum_ofReal_ne_top
  exact ((hwlim.eventually (gt_mem_nhds hc)).and
    (hflim.eventually (gt_mem_nhds hc))).exists

/-- A finite prescribed coefficient error and a small infinite-tail energy
occur together with positive probability. -/
theorem gaussian_head_and_tail_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Finset ι) (f : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) {c : ℝ≥0∞}
    (hmean : (∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (w i)) < c) :
    0 < Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))
      ({g | (∑ i : S, ‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2) < δ} ∩
        {g | gaussianTailEnergy w S g < c}) := by
  classical
  let A : Set (S → ℂ) :=
    {z | (∑ i : S, ‖(Real.sqrt (w i) : ℂ) * z i - f i‖ ^ 2) < δ}
  let B : Set (↥((S : Set ι)ᶜ) → ℂ) :=
    {z | (∑' i : ↥((S : Set ι)ᶜ),
      ENNReal.ofReal (w i) * ENNReal.ofReal (Complex.normSq (z i))) < c}
  have hmA : MeasurableSet A := by
    apply measurableSet_lt <;> fun_prop
  have hmB : MeasurableSet B := by
    apply measurableSet_lt
    · apply Measurable.tsum
      intro i
      fun_prop
    · exact measurable_const
  have hindep : IndepSet
      {g | (∑ i : S, ‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2) < δ}
      {g | gaussianTailEnergy w S g < c}
      (Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))) := by
    exact (indepFun_iff_indepSet_preimage (by fun_prop) (by fun_prop)).mp
      (independent_product_head_tail (fun _ : ι => complexGaussian (1 / 2)) S)
      A B hmA hmB
  rw [hindep.measure_inter_eq_mul]
  apply ENNReal.mul_pos
  · have hpos := weighted_gaussian_head_open_pos S (v := 1 / 2) (by norm_num)
      (fun i => (Real.sqrt (w i) : ℂ))
      (fun i => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw i)).ne')
      {z : S → ℂ | (∑ i : S, ‖z i - f i‖ ^ 2) < δ}
      (by apply isOpen_lt <;> fun_prop) ⟨fun i => f i, by simpa using hδ⟩
    exact hpos.ne'
  · exact (gaussianTailEnergy_small_pos w S hmean).ne'

end CountableProduct

end DefocusingNLS

end OAI
