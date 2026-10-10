import OAI.Geometry.Immersion.ClosedSurface.ModeDifferences
import OAI.Geometry.Immersion.ClosedSurface.MeanError

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma gradientAmplitude_congr {n : ℕ} (τ : ℝ) {Z W : Field n} {p : Base}
    (he : Z =ᶠ[nhds p] W) (v : Base) : gradientAmplitude τ Z v p = gradientAmplitude τ W v p := by
  simp only [gradientAmplitude, coordDeriv, he.fderiv_eq, he.self_of_nhds]

lemma gradientAmplitude_sub {n : ℕ} (τ : ℝ) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (v : Base) :
    gradientAmplitude τ (fun p => Z p - W p) v p =
      gradientAmplitude τ Z v p - gradientAmplitude τ W v p := by
  rw [gradientAmplitude, partial_sub hZ hW]
  ext i
  simp only [gradientAmplitude, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma gradientAmplitude_free_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v : Base) :
    EqOn (gradientAmplitude τ (modeApprox τ G (fun p => V p - W p) (fun _ => 0) q) v)
      (fun p => gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p -
        gradientAmplitude τ (modeApprox τ G W (fun _ => 0) q) v p) U := by
  have he := modeApprox_sub τ hG h hV hW (f := fun _ => 0) (g := fun _ => 0)
    contDiffOn_const contDiffOn_const q
  simp only [sub_self] at he
  have hZ := contDiffOn_modeApprox τ h hV (f := fun _ => 0) contDiffOn_const q
  have hY := contDiffOn_modeApprox τ h hW (f := fun _ => 0) contDiffOn_const q
  intro p hp
  have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
  rw [gradientAmplitude_congr τ hee,
    gradientAmplitude_sub τ (((hZ p hp).contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by simp))
      (((hY p hp).contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by simp))]

lemma leadingDerivative_sub {n : ℕ} (τ : ℝ) (V W : Field n) (v : Base) (p : Base) :
    leadingDerivative τ (fun p => V p - W p) v p =
      leadingDerivative τ V v p - leadingDerivative τ W v p := by
  simp only [leadingDerivative, smul_sub]

lemma contDiffOn_modeMeanError {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (h : ModeDomain G U) (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U)
    (q : ℕ) (v w : Base) : ContDiffOn ℝ ∞ (modeMeanError τ G V W q v w) U := by
  have hZ := contDiffOn_gradientAmplitude h.isOpen
    (contDiffOn_modeApprox τ h hV (f := fun _ => 0) contDiffOn_const q) τ v
  have hY := contDiffOn_gradientAmplitude h.isOpen
    (contDiffOn_modeApprox τ h hW (f := fun _ => 0) contDiffOn_const q) τ w
  exact (ClosedSurfaceR4.QuadraticMean.contDiffOn_zeroPair hZ hY).sub
    (ClosedSurfaceR4.QuadraticMean.contDiffOn_zeroPair
      (contDiffOn_leadingDerivative τ hV v) (contDiffOn_leadingDerivative τ hW w))

lemma modeMeanError_sub_left {n : ℕ} (τ : ℝ) {G V W Z : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (modeMeanError τ G (fun p => V p - W p) Z q v w)
      (fun p => modeMeanError τ G V Z q v w p - modeMeanError τ G W Z q v w p) U := by
  intro p hp
  unfold modeMeanError
  rw [gradientAmplitude_free_sub τ hG h hV hW q v hp, leadingDerivative_sub,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_left,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_left]
  ring

lemma modeMeanError_sub_right {n : ℕ} (τ : ℝ) {G V W Z : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (modeMeanError τ G Z (fun p => V p - W p) q v w)
      (fun p => modeMeanError τ G Z V q v w p - modeMeanError τ G Z W q v w p) U := by
  intro p hp
  unfold modeMeanError
  rw [gradientAmplitude_free_sub τ hG h hV hW q w hp, leadingDerivative_sub,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_right,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_right]
  ring

lemma modeMeanError_difference {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (fun p => modeMeanError τ G V V q v w p - modeMeanError τ G W W q v w p)
      (fun p => modeMeanError τ G (fun p => V p - W p) V q v w p +
        modeMeanError τ G W (fun p => V p - W p) q v w p) U := by
  intro p hp
  dsimp only
  rw [modeMeanError_sub_left τ hG h hV hW q v w hp,
    modeMeanError_sub_right τ hG h hV hW q v w hp]
  ring




theorem weighted_modeMeanError_difference {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V W : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C D : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (hbW : WeightedBound U s (m + q + 2) C W)
    (hbDiff : WeightedBound U s (m + q + 2) D (fun p => V p - W p))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (2 * meanErrorConstant n m K q * (C * D / (s * τ)))
      (fun p => modeMeanError τ G V V q v w p - modeMeanError τ G W W q v w p) := by
  have h1 := weighted_modeMeanError hτ hG h hs hτs hs1 hK hD hC (hV.sub hW) hV q m
    hc hbDiff hbV v w hv hw
  have h2 := weighted_modeMeanError hτ hG h hs hτs hs1 hK hC hD hW (hV.sub hW) q m
    hc hbW hbDiff v w hv hw
  have hh := h1.add h.isOpen.uniqueDiffOn hs.le
    (contDiffOn_modeMeanError τ h (hV.smooth.sub hW.smooth) hV.smooth q v w)
    (contDiffOn_modeMeanError τ h hW.smooth (hV.smooth.sub hW.smooth) q v w) h2
  have he : meanErrorConstant n m K q * (D * C / (s * τ)) +
      meanErrorConstant n m K q * (C * D / (s * τ)) =
      2 * meanErrorConstant n m K q * (C * D / (s * τ)) := by ring
  rw [he] at hh
  exact hh.congr (modeMeanError_difference τ hG h hV.smooth hW.smooth q v w)

end ClosedSurfaceR4.SmallModes

end

end OAI
