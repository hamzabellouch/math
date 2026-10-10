import OAI.Geometry.Immersion.ClosedSurface.MeanError

namespace OAI

/-! Gradient and quadratic-mean estimates from an actual amplitude's
size and its distance to the normal seed. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open WeightedEstimates

lemma weighted_gradient_seed_error {n : ℕ} {τ s C E : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hC : 0 ≤ C) (hE : 0 ≤ E) {Z V : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (he : WeightedBound U s m E (fun p => Z p - V p))
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (C / s + E / τ)
      (fun p => gradientAmplitude τ Z v p - leadingDerivative τ V v p) := by
  have hd := hbZ.directional hU hs hZ v
  have hd' : WeightedBound U s m (C / s) (coordDeriv v Z) := by
    apply hd.mono_const
    exact mul_le_of_le_one_left (div_nonneg hC hs.le) hv
  have hl := weighted_leadingDerivative hτ hU.uniqueDiffOn hs hE (hZ.sub hV) he v hv
  have hh := hd'.add hU.uniqueDiffOn hs.le (contDiffOn_coordDeriv_vector hU hZ v)
    (contDiffOn_leadingDerivative τ (hZ.sub hV) v) hl
  apply hh.congr
  intro p _
  exact gradientAmplitude_sub_leading τ Z V v p

lemma weighted_gradient_from_seed {n : ℕ} {τ s C E D : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 0 ≤ D) {Z V : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (he : WeightedBound U s m E (fun p => Z p - V p))
    (hbV : WeightedBound U s m D V)
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (C / s + E / τ + D / τ) (gradientAmplitude τ Z v) := by
  have he' := weighted_gradient_seed_error hU hτ hs hC hE hZ hV hbZ he v hv
  have hl := weighted_leadingDerivative hτ hU.uniqueDiffOn hs hD hV hbV v hv
  have hh := he'.add hU.uniqueDiffOn hs.le
    ((contDiffOn_gradientAmplitude hU hZ τ v).sub (contDiffOn_leadingDerivative τ hV v))
    (contDiffOn_leadingDerivative τ hV v) hl
  exact hh.congr (fun _ _ => (sub_add_cancel _ _).symm)

lemma weighted_mean_from_seed {n : ℕ} {τ s C E D C' E' D' : ℝ} {m : ℕ}
    {U : Set Base} (hU : IsOpen U) (hτ : 0 < τ) (hs : 0 < s)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hC' : 0 ≤ C') (hE' : 0 ≤ E') (hD' : 0 ≤ D') {Z V W Y : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (hV : ContDiffOn ℝ ∞ V U)
    (hW : ContDiffOn ℝ ∞ W U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbZ : WeightedBound U s (m + 1) C Z)
    (heZ : WeightedBound U s m E (fun p => Z p - V p))
    (hbV : WeightedBound U s m D V)
    (hbW : WeightedBound U s (m + 1) C' W)
    (heW : WeightedBound U s m E' (fun p => W p - Y p))
    (hbY : WeightedBound U s m D' Y)
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m ((n : ℝ) * 2 ^ m *
      ((C / s + E / τ) * (C' / s + E' / τ + D' / τ) + D / τ * (C' / s + E' / τ)))
      (fun p => QuadraticMean.zeroPair (gradientAmplitude τ Z v p) (gradientAmplitude τ W w p) -
        QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ Y w p)) := by
  have hgZ := weighted_gradient_seed_error hU hτ hs hC hE hZ hV hbZ heZ v hv
  have hgW := weighted_gradient_seed_error hU hτ hs hC' hE' hW hY hbW heW w hw
  have hbGW := weighted_gradient_from_seed hU hτ hs hC' hE' hD' hW hY hbW heW hbY w hw
  have hbLV := weighted_leadingDerivative hτ hU.uniqueDiffOn hs hD hV hbV v hv
  exact QuadraticMean.weighted_zeroPair_error hU.uniqueDiffOn hs
    (div_nonneg hD hτ.le)
    (add_nonneg (add_nonneg (div_nonneg hC' hs.le) (div_nonneg hE' hτ.le)) (div_nonneg hD' hτ.le))
    (add_nonneg (div_nonneg hC hs.le) (div_nonneg hE hτ.le))
    (add_nonneg (div_nonneg hC' hs.le) (div_nonneg hE' hτ.le))
    (contDiffOn_leadingDerivative τ hV v) (contDiffOn_leadingDerivative τ hY w)
    (contDiffOn_gradientAmplitude hU hZ τ v) (contDiffOn_gradientAmplitude hU hW τ w)
    hbLV hbGW hgZ hgW

end ClosedSurfaceR4.SmallModes

end

end OAI
