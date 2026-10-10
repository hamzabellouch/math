import OAI.Geometry.Immersion.ClosedSurface.GradientBounds
import OAI.Geometry.Immersion.ClosedSurface.QuadraticError

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates



structure FreeCoefficient {n : ℕ} (G : Field n) (U : Set Base) (V : Field n) : Prop where
  smooth : ContDiffOn ℝ ∞ V U
  perpX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0
  perpY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0
  perpSecond : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0

lemma FreeCoefficient.sub {n : ℕ} {G V W : Field n} {U : Set Base}
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) :
    FreeCoefficient G U (fun p => V p - W p) := by
  refine ⟨hV.smooth.sub hW.smooth, ?_, ?_, ?_⟩
  · intro p hp; simp [dotProduct_sub, hV.perpX p hp, hW.perpX p hp]
  · intro p hp; simp [dotProduct_sub, hV.perpY p hp, hW.perpY p hp]
  · intro p hp; simp [dotProduct_sub, hV.perpSecond p hp, hW.perpSecond p hp]


def leadingDerivative {n : ℕ} (τ : ℝ) (V : Field n) (v : Base) : Field n :=
  fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p

lemma contDiffOn_leadingDerivative {n : ℕ} (τ : ℝ) {V : Field n} {U : Set Base}
    (hV : ContDiffOn ℝ ∞ V U) (v : Base) :
    ContDiffOn ℝ ∞ (leadingDerivative τ V v) U := by
  unfold leadingDerivative
  simpa only [Pi.smul_def'] using
    (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul hV

lemma weighted_leadingDerivative {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {V : Field n}
    {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} (hs : 0 < s)
    (hC : 0 ≤ C) (hV : ContDiffOn ℝ ∞ V U) (hb : WeightedBound U s m C V)
    (v : Base) (hv : ‖v‖ ≤ 1) : WeightedBound U s m (C / τ) (leadingDerivative τ V v) := by
  have hh := hb.complex_smul_pi hU hs hC hV (Complex.I / (τ : ℂ) * (v.1 : ℂ))
  apply hh.mono_const
  have hn : ‖Complex.I / (τ : ℂ) * (v.1 : ℂ)‖ ≤ 1 / τ := by
    rw [norm_mul, norm_div]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    exact mul_le_of_le_one_right (div_nonneg zero_le_one hτ.le)
      (by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using mul_le_mul_of_nonneg_right hn hC

lemma weighted_gradient_free {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hV : FreeCoefficient G U V) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m ((1 + gradientErrorConstant n m K q) * (C / τ))
      (gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v) := by
  have he := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hC
    hV.smooth hV.perpX hV.perpY hV.perpSecond q m hc hbV v hv
  have hl := weighted_leadingDerivative hτ h.isOpen.uniqueDiffOn hs hC hV.smooth
    (hbV.mono_order (show m ≤ m + q + 2 by omega)) v hv
  have hE := (gradientErrorConstant_pos n m q hK).le
  have hZ := contDiffOn_modeApprox τ h hV.smooth (f := fun _ => 0) contDiffOn_const q
  have hsZ := contDiffOn_gradientAmplitude h.isOpen hZ τ v
  have hsL := contDiffOn_leadingDerivative τ hV.smooth v
  have ha := he.add h.isOpen.uniqueDiffOn hs.le (hsZ.sub hsL) hsL hl
  have ha' := ha.congr (fun p _ => (sub_add_cancel _ _).symm)
  apply ha'.mono_const
  have hdiv : C / s ≤ C / τ := div_le_div_of_nonneg_left hC hτ hτs
  nlinarith [mul_le_mul_of_nonneg_left hdiv hE]



def modeMeanError {n : ℕ} (τ : ℝ) (G V W : Field n) (q : ℕ) (v w : Base) : Base → ℝ :=
  fun p => ClosedSurfaceR4.QuadraticMean.zeroPair
      (gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p)
      (gradientAmplitude τ (modeApprox τ G W (fun _ => 0) q) w p) -
    ClosedSurfaceR4.QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ W w p)

def meanErrorConstant (n m : ℕ) (K : ℝ) (q : ℕ) : ℝ :=
  (n : ℝ) * 2 ^ m * gradientErrorConstant n m K q * (2 + gradientErrorConstant n m K q)

lemma meanErrorConstant_nonneg (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ meanErrorConstant n m K q := by
  have hE := (gradientErrorConstant_pos n m q hK).le
  unfold meanErrorConstant
  positivity




theorem weighted_modeMeanError {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V W : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C D : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (hbW : WeightedBound U s (m + q + 2) D W)
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (meanErrorConstant n m K q * (C * D / (s * τ)))
      (modeMeanError τ G V W q v w) := by
  have hE := (gradientErrorConstant_pos n m q hK).le
  have hZV := contDiffOn_modeApprox τ h hV.smooth (f := fun _ => 0) contDiffOn_const q
  have hZW := contDiffOn_modeApprox τ h hW.smooth (f := fun _ => 0) contDiffOn_const q
  have hA := contDiffOn_leadingDerivative τ hV.smooth v
  have hB := contDiffOn_leadingDerivative τ hW.smooth w
  have hZ := contDiffOn_gradientAmplitude h.isOpen hZV τ v
  have hY := contDiffOn_gradientAmplitude h.isOpen hZW τ w
  have hbA := weighted_leadingDerivative hτ h.isOpen.uniqueDiffOn hs hC hV.smooth
    (hbV.mono_order (show m ≤ m + q + 2 by omega)) v hv
  have hbY := weighted_gradient_free hτ hG h hs hτs hs1 hK hD hW q m hc hbW w hw
  have heZ := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hC
    hV.smooth hV.perpX hV.perpY hV.perpSecond q m hc hbV v hv
  have heY := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hD
    hW.smooth hW.perpX hW.perpY hW.perpSecond q m hc hbW w hw
  have hnC : 0 ≤ C / τ := div_nonneg hC hτ.le
  have hnD : 0 ≤ (1 + gradientErrorConstant n m K q) * (D / τ) := by positivity
  have hnE : 0 ≤ gradientErrorConstant n m K q * (C / s) := by positivity
  have hnF : 0 ≤ gradientErrorConstant n m K q * (D / s) := by positivity
  have hh := ClosedSurfaceR4.QuadraticMean.weighted_zeroPair_error h.isOpen.uniqueDiffOn hs
    hnC hnD hnE hnF hA hB hZ hY hbA hbY heZ heY
  have heq : (n : ℝ) * 2 ^ m *
      (gradientErrorConstant n m K q * (C / s) *
        ((1 + gradientErrorConstant n m K q) * (D / τ)) +
        C / τ * (gradientErrorConstant n m K q * (D / s))) =
      meanErrorConstant n m K q * (C * D / (s * τ)) := by
    unfold meanErrorConstant
    ring
  rw [heq] at hh
  exact hh

end ClosedSurfaceR4.SmallModes

end

end OAI
