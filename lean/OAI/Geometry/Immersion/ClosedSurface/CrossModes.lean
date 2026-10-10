import OAI.Geometry.Immersion.ClosedSurface.DoubleModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude conjugate displacement
  doublePair crossPair realMode sumDisplacement quadraticMetric quadraticMetric_expansion
  differentiableAt_displacement)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)


def phaseZeroTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : SmallModes.Field n) :
    Base → PhaseMean.Tensor :=
  fun p i => zeroPair (derivativeAmplitude τ φ Z (firstDirection i) p)
    (derivativeAmplitude τ φ Z (secondDirection i) p)


def phaseDoubleTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    derivativeAmplitude τ φ Z (secondDirection i) p) / 2

def phasePlusTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    derivativeAmplitude τ ψ W (secondDirection i) p) / 2

def phaseMinusTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    conjugate (derivativeAmplitude τ ψ W (secondDirection i) p)) / 2

lemma displacement_doubleTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ)
    (Z : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => 2 * φ q) (phaseDoubleTensor τ φ Z) p i =
      doublePair (φ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ φ Z (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseDoubleTensor, Pi.smul_apply, smul_eq_mul,
    ← mul_div_assoc, Complex.div_ofNat_re, doublePair]

lemma displacement_crossTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ)
    (Z W : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => φ q - ψ q) (phaseMinusTensor τ φ ψ Z W) p i +
      displacement τ (fun q => φ q + ψ q) (phasePlusTensor τ φ ψ Z W) p i =
      crossPair (φ p / τ) (ψ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ ψ W (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseMinusTensor, phasePlusTensor,
    Pi.smul_apply, smul_eq_mul, sub_div, add_div,
    ← mul_div_assoc, Complex.div_ofNat_re, crossPair]

def zeroPhaseSum {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → SmallModes.Field n) : Base → PhaseMean.Tensor :=
  fun p => ∑ i, phaseZeroTensor τ (φ i) (Z i) p

def nonzeroPhaseSum {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → SmallModes.Field n) : Base → PhaseMean.Tensor :=
  fun p => (∑ i, displacement τ (fun q => 2 * φ i q) (phaseDoubleTensor τ (φ i) (Z i)) p) +
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (displacement τ (fun q => φ i q - φ j q) (phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)) p +
        displacement τ (fun q => φ i q + φ j q) (phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)) p)



lemma realMetric_sumDisplacement {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → Base → ℝ} {Z : ι → SmallModes.Field n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p) (τ : ℝ) :
    realMetricTensor (sumDisplacement τ φ Z) p = zeroPhaseSum τ φ Z p +
      nonzeroPhaseSum τ φ Z p := by
  ext k
  rw [realMetricTensor_apply]
  change quadraticMetric (sumDisplacement τ φ Z) (firstDirection k) (secondDirection k) p = _
  rw [quadraticMetric_expansion τ hφ hZ]
  simp only [zeroPhaseSum, nonzeroPhaseSum, phaseZeroTensor, QuadraticMean.meanMetric, Pi.add_apply, Finset.sum_apply,
    displacement_doubleTensor, displacement_crossTensor]
  ring

lemma realLinearized_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (F : RField n) {X : ι → RField n} {p : Base}
    (hX : ∀ i, DifferentiableAt ℝ (X i) p) :
    realLinearizedTensor F (fun q => ∑ i, X i q) p = ∑ i, realLinearizedTensor F (X i) p := by
  ext k
  simp only [Finset.sum_apply, realLinearizedTensor_apply, realLinearized, coordDeriv,
    fderiv_fun_sum (fun i _ => hX i), sum_apply,
    dotProduct_sum, Finset.sum_add_distrib]



theorem finite_phase_metric_identity {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F V : RField n} {φ : ι → Base → ℝ} {Z : ι → SmallModes.Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hV : DifferentiableAt ℝ V p)
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p)
    (τ : ℝ) (H : Base → PhaseMean.Tensor) :
    let U := sumDisplacement τ φ Z
    realMetricTensor (fun q => F q + (U q + V q)) p - realMetricTensor F p - H p =
      realLinearizedTensor F U p +
      (realLinearizedTensor F V p + nonzeroPhaseSum τ φ Z p) +
      (realLinearizedTensor U V p + realMetricTensor V p) +
      (zeroPhaseSum τ φ Z p - H p) := by
  dsimp only
  have hU : DifferentiableAt ℝ (sumDisplacement τ φ Z) p := by
    exact DifferentiableAt.fun_sum fun i _ => differentiableAt_displacement (hφ i) (hZ i) τ
  have hUV : DifferentiableAt ℝ (fun q => sumDisplacement τ φ Z q + V q) p := hU.add hV
  rw [realMetricTensor_add hF hUV, realMetricTensor_add hU hV,
    realMetric_sumDisplacement hφ hZ]
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, realLinearizedTensor_apply, realLinearized_add_right hU hV]
  ring

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma contDiffOn_derivativeAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → CVec n} (hφ : ContDiffOn ℝ ∞ φ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) (v : Base) :
    ContDiffOn ℝ ∞ (derivativeAmplitude τ φ Z v) U := by
  have hdφ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hφ v
  have hdZ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hZ v
  have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn hdφ
  change ContDiffOn ℝ ∞ (fun p => fderiv ℝ Z p v +
    (Complex.I / (τ : ℂ) * ((fderiv ℝ φ p v : ℝ) : ℂ)) • Z p) U
  exact hdZ.add (((contDiffOn_const (c := Complex.I / (τ : ℂ))).mul hc).smul hZ)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




lemma weighted_derivativeAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → CVec n} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (derivativeAmplitude τ φ Z v) := by
  have hd := (hb.directional hU hs hZ v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hdφ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hφ v
  have hc := weighted_real_complex hU.uniqueDiffOn hs.le hP hdφ hp
  have hcs := Complex.ofRealCLM.contDiff.comp_contDiffOn hdφ
  have hc' := hc.const_mul hU.uniqueDiffOn hcs (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ)) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) U := by
    exact contDiffOn_const.mul hcs
  have hz := ClosedSurfaceR4.SmallModes.weighted_smul_field hU.uniqueDiffOn hs
    (show 0 ≤ 1 / τ * P by positivity) hC hcm hZ hc'
    (hb.mono_order (Nat.le_succ m))
  have hzs : ContDiffOn ℝ ∞
      (fun p => (Complex.I / (τ : ℂ) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) • Z p) U := by
    exact hcm.smul hZ
  have ha := hd'.add hU.uniqueDiffOn hs.le
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hZ v) hzs hz
  convert ha using 1 <;> first | rfl | ring

lemma weighted_halfDot {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {X Y : Base → CVec n} {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : WeightedBound U s m C X) (hbY : WeightedBound U s m D Y) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * C * D)) (fun p => (X p ⬝ᵥ Y p) / 2) := by
  have hh := (hbX.dot hU hs hC hD hX hY hbY).const_mul hU (contDiffOn_dot hX hY) (1 / 2 : ℂ)
  apply (hh.congr (fun p _ => by ring)).mono_const
  simp only [norm_div, norm_one, Complex.norm_ofNat, Fintype.card_fin]
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * C * D) := by positivity
  nlinarith

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_phasePlusTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (phasePlusTensor τ φ ψ Z W) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact (contDiffOn_dot (QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ _)
    (QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ _)).div_const 2

lemma contDiffOn_phaseMinusTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (phaseMinusTensor τ φ ψ Z W) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact (contDiffOn_dot (QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ _)
    (QuadraticMean.contDiffOn_conjugate
      (QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ _))).div_const 2



theorem weighted_phaseCrossTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} {τ s C D P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (hbZ : WeightedBound U s (m + 1) C Z) (hbW : WeightedBound U s (m + 1) D W)
    (hpφ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ))
    (hpψ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v ψ)) :
    let A := (1 + 2 ^ m * P) * C / τ
    let B := (1 + 2 ^ m * P) * D / τ
    WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phasePlusTensor τ φ ψ Z W) ∧
      WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phaseMinusTensor τ φ ψ Z W) := by
  dsimp only
  have hA : 0 ≤ (1 + 2 ^ m * P) * C / τ := by positivity
  have hB : 0 ≤ (1 + 2 ^ m * P) * D / τ := by positivity
  have hdZ (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hC hP hφ hZ hbZ v hv (hpφ v hv)
  have hdW (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hD hP hψ hW hbW v hv (hpψ v hv)
  have hsZ (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ v
  have hsW (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ v
  constructor
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phasePlusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _) (hsW _)
        (hdZ _ (norm_firstDirection i)) (hdW _ (norm_secondDirection i))
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phaseMinusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _)
        (QuadraticMean.contDiffOn_conjugate (hsW _)) (hdZ _ (norm_firstDirection i))
        (QuadraticMean.weighted_conjugate hU.uniqueDiffOn hs hB (hsW _)
          (hdW _ (norm_secondDirection i)))

end ClosedSurfaceR4.RealModes

end

end OAI
