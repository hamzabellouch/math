import OAI.Geometry.RCD.Heat.HeatTransitionPointwise
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Heat displacement of a function with bounded weak Laplacian

The semigroup derivative and conservation control its pairing with every
nonnegative L¹ ∩ L² test. This is the input for short-time concentration
of the constructed transition measures.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_bounded_laplacian_pairing
    (g : SobolevSpace (hausdorff n X) hX.quadratic)
    (dg : Lp ℝ 2 (hausdorff n X)) (hg : IsWeakLaplacian (hausdorff n X) hX.quadratic g dg)
    {B : ℝ} (_hB : 0 ≤ B) (hdg : ∀ᵐ x ∂hausdorff n X, |dg x| ≤ B)
    (f : Lp ℝ 2 (hausdorff n X)) (hf : 0 ≤ f) (hfi : Integrable f (hausdorff n X))
    {t : ℝ} (ht : 0 ≤ t) :
    |inner ℝ (heatAt (hausdorff n X) hX.quadratic t f - f)
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic g)| ≤
        t * B * ∫ x, f x ∂hausdorff n X := by
  let μ := hausdorff n X
  let A (s : ℝ) := inner ℝ (heatAt μ hX.quadratic s f) (SobolevSpace.toLp μ hX.quadratic g)
  let E (s : ℝ) := inner ℝ (heatGeneratorAt μ hX.quadratic s f)
    (SobolevSpace.toLp μ hX.quadratic g)
  have hAc : ContinuousOn A (Ici 0) :=
    ((heatAt_continuous μ hX.quadratic f).inner continuous_const).continuousOn
  have hAd (s : ℝ) (hs : 0 < s) : HasDerivAt A (-E s) s := by
    have hd := (heatAt_hasDerivAt μ hX.quadratic s hs f).inner ℝ
      (hasDerivAt_const s (SobolevSpace.toLp μ hX.quadratic g))
    simpa only [A, E, inner_neg_left, inner_zero_right, add_zero, zero_add] using hd
  have hEI (s : ℝ) (hs : 0 < s) : |E s| ≤ 0 * (0 : ℝ) + B * ∫ x, f x ∂μ := by
    have he : E s = -inner ℝ (heatAt μ hX.quadratic s f) dg := by
      dsimp only [E]
      rw [heatGeneratorAt_of_pos μ hX.quadratic s hs, ← heatGenerator_form,
        energyForm_comm, hg, heatSobolev_toLp, real_inner_comm dg]
    have hpos := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic s f hf)
    have hi := (Lp.memLp (heatAt μ hX.quadratic s f)).integrable_mul (Lp.memLp dg)
    have him := heatAt_integrable_of_nonneg μ hX.quadratic s f hf hfi
    have hmass : (∫ x, heatAt μ hX.quadratic s f x ∂μ) = ∫ x, f x ∂μ :=
      hX.conservative K n hn p f hf hfi s hs.le
    rw [he, abs_neg, L2.inner_def]
    simp only [Real.inner_apply, zero_mul, zero_add]
    calc
      _ ≤ ∫ x, |heatAt μ hX.quadratic s f x * dg x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, B * heatAt μ hX.quadratic s f x ∂μ := by
        apply integral_mono_ae hi.abs (him.const_mul B)
        filter_upwards [hpos, hdg] with x hx hdx
        change |heatAt μ hX.quadratic s f x * dg x| ≤ B * heatAt μ hX.quadratic s f x
        rw [abs_mul, abs_of_nonneg hx, mul_comm B]
        exact mul_le_mul_of_nonneg_left hdx hx
      _ = _ := by rw [integral_const_mul, hmass]
  have hh := abs_sub_le_potential_drop hAc (continuousOn_const (c := (0 : ℝ))) hAd
    (fun s _ => by simpa only [neg_zero] using hasDerivAt_const s (0 : ℝ)) hEI ht
  simpa only [A, heatAt_zero, one_apply_eq_self, sub_zero, zero_mul, zero_add,
    inner_sub_left, mul_assoc, mul_comm, mul_left_comm] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
