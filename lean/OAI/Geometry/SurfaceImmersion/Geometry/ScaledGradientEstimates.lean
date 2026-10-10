import OAI.Geometry.SurfaceImmersion.Geometry.GradientSeedEstimates

namespace OAI

/-! Extract the common small factor from the quadratic-mean error. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open WeightedEstimates

lemma weighted_gradient_small_error {n : ℕ} {τ s η C D : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hη : 0 ≤ η) (hratio : τ / s ≤ η) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {Z V : Field n} (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (he : WeightedBound U s m (η * D) (fun p => Z p - V p))
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (η * (C + D) / τ)
      (fun p => gradientAmplitude τ Z v p - leadingDerivative τ V v p) := by
  apply (weighted_gradient_seed_error hU hτ hs hC (mul_nonneg hη hD) hZ hV hbZ he v hv).mono_const
  have hc : C / s ≤ η * C / τ := by
    apply (le_div_iff₀ hτ).2
    calc
      C / s * τ = (τ / s) * C := by ring
      _ ≤ η * C := mul_le_mul_of_nonneg_right hratio hC
  calc
    C / s + η * D / τ ≤ η * C / τ + η * D / τ := add_le_add hc le_rfl
    _ = _ := by ring

lemma weighted_gradient_small {n : ℕ} {τ s η C D B : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hratio : τ / s ≤ η)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    {Z V : Field n} (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (he : WeightedBound U s m (η * D) (fun p => Z p - V p))
    (hbV : WeightedBound U s m B V) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m ((C + D + B) / τ) (gradientAmplitude τ Z v) := by
  have hg := weighted_gradient_small_error hU hτ hs hη hratio hC hD hZ hV hbZ he v hv
  have hl := weighted_leadingDerivative hτ hU.uniqueDiffOn hs hB hV hbV v hv
  have hh := hg.add hU.uniqueDiffOn hs.le
    ((contDiffOn_gradientAmplitude hU hZ τ v).sub (contDiffOn_leadingDerivative τ hV v))
    (contDiffOn_leadingDerivative τ hV v) hl
  apply (hh.congr (fun _ _ => (sub_add_cancel _ _).symm)).mono_const
  calc
    η * (C + D) / τ + B / τ ≤ (1 * (C + D)) / τ + B / τ :=
      add_le_add (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hη1 (add_nonneg hC hD)) hτ.le) le_rfl
    _ = _ := by ring

lemma weighted_mean_small_error {n : ℕ} {τ s η C D B C' D' B' : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hratio : τ / s ≤ η)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hC' : 0 ≤ C') (hD' : 0 ≤ D') (hB' : 0 ≤ B')
    {Z V W Y : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hW : ContDiffOn ℝ ∞ W U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (heZ : WeightedBound U s m (η * D) (fun p => Z p - V p))
    (hbV : WeightedBound U s m B V)
    (hbW : WeightedBound U s (m + 1) C' W)
    (heW : WeightedBound U s m (η * D') (fun p => W p - Y p))
    (hbY : WeightedBound U s m B' Y)
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m
      ((n : ℝ) * 2 ^ m * ((C + D) * (C' + D' + B') + B * (C' + D')) * η / τ ^ 2)
      (fun p => QuadraticMean.zeroPair (gradientAmplitude τ Z v p) (gradientAmplitude τ W w p) -
        QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ Y w p)) := by
  have he1 := weighted_gradient_small_error hU hτ hs hη hratio hC hD hZ hV hbZ heZ v hv
  have he2 := weighted_gradient_small_error hU hτ hs hη hratio hC' hD' hW hY hbW heW w hw
  have hw' := weighted_gradient_small hU hτ hs hη hη1 hratio hC' hD' hB' hW hY hbW heW hbY w hw
  have hv' := weighted_leadingDerivative hτ hU.uniqueDiffOn hs hB hV hbV v hv
  have hbound := QuadraticMean.weighted_zeroPair_error hU.uniqueDiffOn hs
    (div_nonneg hB hτ.le) (div_nonneg (add_nonneg (add_nonneg hC' hD') hB') hτ.le)
    (div_nonneg (mul_nonneg hη (add_nonneg hC hD)) hτ.le)
    (div_nonneg (mul_nonneg hη (add_nonneg hC' hD')) hτ.le)
    (contDiffOn_leadingDerivative τ hV v) (contDiffOn_leadingDerivative τ hY w)
    (contDiffOn_gradientAmplitude hU hZ τ v) (contDiffOn_gradientAmplitude hU hW τ w)
    hv' hw' he1 he2
  convert hbound using 1
  ring

end ClosedSurfaceR4.SmallModes

end

end OAI
