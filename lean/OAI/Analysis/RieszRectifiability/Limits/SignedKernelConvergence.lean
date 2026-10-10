import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteRieszPairing
import OAI.Analysis.RieszRectifiability.Limits.LipschitzMomentConvergence

namespace OAI

/-!
# Convergence of signed weighted kernel integrals

Finite step approximations in the second variable reduce weighted product
integrals to sums of weighted moments and cell masses. Integrable absolute
weights and Lipschitz kernel bounds control the approximation error, allowing
convergence of these finite sums to pass to the original kernel integrals.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integrable_weighted_bounded_function (μ : Measure X) (w f : X → ℝ)
    (hw : Integrable w μ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun x => w x * f x) μ := by
  apply (hw.abs.mul_const B).mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖w x * f x‖ ≤ |w x| * B
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg (w x))

theorem integrable_weighted_product_kernel (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Integrable (fun q : X × Y => w q.1 * F q) (μ.prod ν) := by
  have hdom := (hw.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const B
  apply hdom.mono' (hw.aestronglyMeasurable.comp_fst.mul hF.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖w q.1 * F q‖ ≤ (|w q.1| * 1) * B
  rw [Real.norm_eq_abs, abs_mul, mul_one]
  exact mul_le_mul_of_nonneg_left (hB q) (abs_nonneg (w q.1))

variable [Fintype ι]

def secondVariableStep (s : ι → Set Y) (z : ι → Y) (F : X × Y → ℝ) : X × Y → ℝ :=
  fun q => finiteStep s (fun i => F (q.1, z i)) q.2

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem weighted_secondVariableStep_eq_sum (s : ι → Set Y) (z : ι → Y)
    (w : X → ℝ) (F : X × Y → ℝ) (q : X × Y) :
    w q.1 * secondVariableStep s z F q =
      ∑ i, (w q.1 * F (q.1, z i)) * (s i).indicator (fun _ => (1 : ℝ)) q.2 := by
  classical
  unfold secondVariableStep finiteStep
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q.2 ∈ s i
  · simp only [indicator_of_mem h, mul_one]
  · simp only [indicator_of_notMem h, mul_zero]

theorem integrable_weighted_secondVariableStep (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (z : ι → Y)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Integrable (fun q : X × Y => w q.1 * secondVariableStep s z F q) (μ.prod ν) := by
  classical
  simp_rw [weighted_secondVariableStep_eq_sum]
  apply integrable_finsetSum
  intro i _
  exact (integrable_weighted_bounded_function μ w (fun x => F (x, z i)) hw
    (hF.comp (measurable_id.prodMk measurable_const)) B (fun x => hB (x, z i))).mul_prod
      ((integrable_const (μ := ν) (1 : ℝ)).indicator (hs i))

theorem integral_weighted_secondVariableStep (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (z : ι → Y)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    (∫ q : X × Y, w q.1 * secondVariableStep s z F q ∂μ.prod ν) =
      ∑ i, (∫ x, w x * F (x, z i) ∂μ) * ν.real (s i) := by
  classical
  simp_rw [weighted_secondVariableStep_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_weighted_bounded_function μ w (fun x => F (x, z i)) hw
      (hF.comp (measurable_id.prodMk measurable_const)) B (fun x => hB (x, z i))).mul_prod
        ((integrable_const (μ := ν) (1 : ℝ)).indicator (hs i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul (fun x => w x * F (x, z i)) ((s i).indicator (fun _ => (1 : ℝ)))]
  simp only [integral_indicator (hs i), setIntegral_const, smul_eq_mul, mul_one]

variable [MetricSpace X] [MetricSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]

theorem weighted_secondVariableStep_error (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (z : ι → Y) (r : ℝ)
    (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ y ∂ν.restrict (s i), dist y (z i) ≤ r)
    (F : X × Y → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    |(∫ q : X × Y, w q.1 * F q ∂μ.prod ν) -
      ∫ q : X × Y, w q.1 * secondVariableStep s z F q ∂μ.prod ν| ≤
        ((∫ x, |w x| ∂μ) * ν.real univ) * ((K : ℝ) * r) := by
  have hkernel := integrable_weighted_product_kernel μ ν w hw F hF.continuous.measurable B hB
  have hstep := integrable_weighted_secondVariableStep μ ν w hw s hs z F hF.continuous.measurable B hB
  have hdom := (hw.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const ((K : ℝ) * r)
  have hcells : ∀ᵐ y ∂ν, ∀ i, y ∈ s i → dist y (z i) ≤ r :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hs i)).mp (hcell i))
  have hpoint : ∀ᵐ q : X × Y ∂μ.prod ν,
      |w q.1 * F q - w q.1 * secondVariableStep s z F q| ≤
        (|w q.1| * 1) * ((K : ℝ) * r) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hcover,
      Measure.quasiMeasurePreserving_snd.ae hcells] with q hq hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    have hdist : |F q - F (q.1, z i)| ≤ (K : ℝ) * r := by
      have h := hF.dist_le_mul q (q.1, z i)
      rw [show q = (q.1, q.2) from rfl, dist_prod_same_left] at h
      simpa only [Real.dist_eq] using! h.trans (mul_le_mul_of_nonneg_left (hc i hi) K.coe_nonneg)
    change |w q.1 * F q - w q.1 * finiteStep s (fun j => F (q.1, z j)) q.2| ≤ _
    rw [finiteStep_eq_cell s _ hd i q.2 hi, ← mul_sub, abs_mul, mul_one]
    exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
  rw [← integral_sub hkernel hstep]
  calc
    _ ≤ ∫ q : X × Y, |w q.1 * F q - w q.1 * secondVariableStep s z F q| ∂μ.prod ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ q : X × Y, (|w q.1| * 1) * ((K : ℝ) * r) ∂μ.prod ν :=
      integral_mono_ae (hkernel.sub hstep).abs hdom hpoint
    _ = _ := by
      rw [integral_mul_const, integral_prod_mul (fun x => |w x|) (fun _ : Y => (1 : ℝ)), integral_const]
      simp only [smul_eq_mul, mul_one]

omit [Fintype ι] in

theorem weighted_product_kernel_tendsto
    (μ : ℕ → Measure X) (μ₀ : Measure X) (ν : ℕ → Measure Y) (ν₀ : Measure Y)
    [∀ j, SFinite (μ j)] [SFinite μ₀] [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (w : ℕ → X → ℝ) (v : X → ℝ) (hw : ∀ j, Integrable (w j) (μ j)) (hv : Integrable v μ₀)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set Y)
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂ν j, y ∈ ⋃ i, s k i)
    (hcover₀ : ∀ k, ∀ᵐ y ∂ν₀, y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Y) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(ν j).restrict (s k i), dist y (z k i) ≤ r k)
    (hcell₀ : ∀ k i, ∀ᵐ y ∂ν₀.restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (ν j).real (s k i)) atTop (𝓝 (ν₀.real (s k i))))
    (W M : ℝ) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hweight : ∀ᶠ j in atTop, (∫ x, |w j x| ∂μ j) ≤ W)
    (htotal : ∀ᶠ j in atTop, (ν j).real univ ≤ M)
    (F : X × Y → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B)
    (hmoment : ∀ y, Tendsto (fun j => ∫ x, w j x * F (x, y) ∂μ j) atTop
      (𝓝 (∫ x, v x * F (x, y) ∂μ₀))) :
    Tendsto (fun j => ∫ q : X × Y, w j q.1 * F q ∂(μ j).prod (ν j)) atTop
      (𝓝 (∫ q : X × Y, v q.1 * F q ∂μ₀.prod ν₀)) := by
  let P := fun j k => ∫ q : X × Y, w j q.1 * secondVariableStep (s k) (z k) F q
    ∂(μ j).prod (ν j)
  let V := fun k => ∫ q : X × Y, v q.1 * secondVariableStep (s k) (z k) F q ∂μ₀.prod ν₀
  have hV : Tendsto V atTop (𝓝 (∫ q : X × Y, v q.1 * F q ∂μ₀.prod ν₀)) := by
    have hscale : Tendsto (fun k => ((∫ x, |v x| ∂μ₀) * ν₀.real univ) * ((K : ℝ) * r k))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using! (hrzero.const_mul (K : ℝ)).const_mul
        ((∫ x, |v x| ∂μ₀) * ν₀.real univ)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hscale.eventually (gt_mem_nhds hε)] with k hk
    rw [Real.dist_eq, abs_sub_comm]
    exact (weighted_secondVariableStep_error μ₀ ν₀ v hv (s k) (hs k) (hd k) (z k) (r k)
      (hcover₀ k) (hcell₀ k) F K hF B hB).trans_lt hk
  have hP : ∀ k, Tendsto (fun j => P j k) atTop (𝓝 (V k)) := by
    intro k
    dsimp only [P, V]
    simp_rw [integral_weighted_secondVariableStep _ _ _ (hw _) (s k) (hs k) (z k)
      F hF.continuous.measurable B hB,
      integral_weighted_secondVariableStep μ₀ ν₀ v hv (s k) (hs k) (z k)
        F hF.continuous.measurable B hB]
    exact tendsto_finsetSum _ fun i _ => (hmoment (z k i)).mul (hmass k i)
  apply tendsto_of_squared_approximation _ P V (fun k => (W * M * ((K : ℝ) * r k)) ^ 2) _ hV
    (by simpa only [mul_zero, zero_pow two_ne_zero] using!
      (((hrzero.const_mul (K : ℝ)).const_mul (W * M)).pow 2)) hP
  intro k
  filter_upwards [hweight, htotal, hcell k] with j hjW hjM hjcell
  have herr := weighted_secondVariableStep_error (μ j) (ν j) (w j) (hw j)
    (s k) (hs k) (hd k) (z k) (r k) (hcover k j) hjcell F K hF B hB
  have hcoef : ((∫ x, |w j x| ∂μ j) * (ν j).real univ) * ((K : ℝ) * r k) ≤
      W * M * ((K : ℝ) * r k) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul hjW hjM (by positivity) hW)
      (mul_nonneg K.coe_nonneg (hr k))
  have hnonneg : 0 ≤ W * M * ((K : ℝ) * r k) :=
    mul_nonneg (mul_nonneg hW hM) (mul_nonneg K.coe_nonneg (hr k))
  simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr (herr.trans hcoef)

end

end RieszRectifiability

end OAI
