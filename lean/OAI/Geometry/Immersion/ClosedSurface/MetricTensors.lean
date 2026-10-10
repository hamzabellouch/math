import OAI.Geometry.Immersion.ClosedSurface.MeanSupport
import OAI.Geometry.Immersion.ClosedSurface.ForcedModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realMetricTensor_apply {n : ℕ} (F : RField n) (p : Base) (i : Fin 3) :
    realMetricTensor F p i = realMetric F (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

def zeroTensor {n : ℕ} (τ : ℝ) (Z : Field n) : Base → Fin 3 → ℝ :=
  fun p i => QuadraticMean.zeroPair (gradientAmplitude τ Z (firstDirection i) p)
    (gradientAmplitude τ Z (secondDirection i) p)


def doubleTensor {n : ℕ} (τ : ℝ) (Z : Field n) : SmallModes.Tensor :=
  fun p i => (gradientAmplitude τ Z (firstDirection i) p ⬝ᵥ
    gradientAmplitude τ Z (secondDirection i) p) / 2

lemma coordDeriv_realOsc {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    coordDeriv v (realOsc τ Z) p = QuadraticMean.realMode (p.1 / τ)
      (gradientAmplitude τ Z v p) := by
  rw [realOsc_eq_displacement]
  exact (QuadraticMean.derivative_displacement differentiableAt_fst hZ τ v).trans
    (congrArg (QuadraticMean.realMode (p.1 / τ)) (gradientAmplitude_eq τ Z v p).symm)

lemma unitMode_half (τ : ℝ) (p : Base) :
    unitMode (τ / 2) p = QuadraticMean.phase (2 * (p.1 / τ)) := by
  simp only [unitMode, QuadraticMean.phase, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_div]
  congr 1
  by_cases ht : τ = 0
  · simp [ht]
  · have ht' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    field_simp



lemma realMetric_realOsc {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    realMetricTensor (realOsc τ Z) p = zeroTensor τ Z p + realOsc (τ / 2) (doubleTensor τ Z) p := by
  ext i
  rw [realMetricTensor_apply, realMetric, coordDeriv_realOsc hZ, coordDeriv_realOsc hZ,
    QuadraticMean.realMode_self_phase]
  simp only [Pi.add_apply, zeroTensor, QuadraticMean.zeroPair, realOsc, QuadraticMean.realPart,
    oscillate, Pi.smul_apply, smul_eq_mul, doubleTensor, unitMode_half]
  rw [← mul_div_assoc (QuadraticMean.phase (2 * (p.1 / τ)))
    (gradientAmplitude τ Z (firstDirection i) p ⬝ᵥ gradientAmplitude τ Z (secondDirection i) p)
    (2 : ℂ), Complex.div_ofNat_re]

lemma contDiffOn_doubleTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {Z : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) : ContDiffOn ℝ ∞ (doubleTensor τ Z) U := by
  apply contDiffOn_pi.mpr
  intro i
  have ha := contDiffOn_gradientAmplitude hU hZ τ (firstDirection i)
  have hb := contDiffOn_gradientAmplitude hU hZ τ (secondDirection i)
  change ContDiffOn ℝ ∞ (fun p => (∑ j, gradientAmplitude τ Z (firstDirection i) p j *
    gradientAmplitude τ Z (secondDirection i) p j) / 2) U
  exact (ContDiffOn.sum fun j _ => (contDiffOn_pi.mp ha j).mul (contDiffOn_pi.mp hb j)).div_const 2



lemma weighted_gradientAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {Z : Field n} {τ s C : ℝ} {m : ℕ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s (m + 1) C Z)
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (2 * C / τ) (gradientAmplitude τ Z v) := by
  have hd := hb.directional hU hs hZ v
  have hd' : WeightedBound U s m (C / τ) (coordDeriv v Z) := by
    apply hd.mono_const
    calc
      _ ≤ C / s := by simpa using mul_le_of_le_one_left (div_nonneg hC hs.le) hv
      _ ≤ C / τ := div_le_div_of_nonneg_left hC hτ hτs
  have hz := (hb.mono_order (show m ≤ m + 1 by omega)).complex_smul_pi
    hU.uniqueDiffOn hs hC hZ (Complex.I / (τ : ℂ) * (v.1 : ℂ))
  have hn : ‖Complex.I / (τ : ℂ) * (v.1 : ℂ)‖ ≤ 1 / τ := by
    rw [norm_mul, norm_div]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    exact mul_le_of_le_one_right (by positivity)
      (by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv)
  have hz' : WeightedBound U s m (C / τ)
      (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p) := by
    apply hz.mono_const
    calc
      _ ≤ (1 / τ) * C := mul_le_mul_of_nonneg_right hn hC
      _ = C / τ := by ring
  have hzs : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p) U := by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul hZ
  change WeightedBound U s m (2 * C / τ)
    (fun p => coordDeriv v Z p + (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p)
  convert hd'.add hU.uniqueDiffOn hs.le (contDiffOn_coordDeriv_vector hU hZ v) hzs hz' using 1
  ring

lemma contDiffOn_dot {n : ℕ} {U : Set Base} {X Y : Field n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (fun p => X p ⬝ᵥ Y p) U := by
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.mp hX i).mul (contDiffOn_pi.mp hY i)

lemma norm_firstDirection (i : Fin 3) : ‖firstDirection i‖ ≤ 1 := by
  fin_cases i <;> norm_num [firstDirection, dx, dy, Prod.norm_def]

lemma norm_secondDirection (i : Fin 3) : ‖secondDirection i‖ ≤ 1 := by
  fin_cases i <;> norm_num [secondDirection, dx, dy, Prod.norm_def]

lemma weighted_doubleTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {Z : Field n} {τ s C : ℝ} {m : ℕ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s (m + 1) C Z) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * (2 * C / τ) * (2 * C / τ)))
      (doubleTensor τ Z) := by
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * (2 * C / τ) * (2 * C / τ)) := by positivity
  apply WeightedBound.pi hU.uniqueDiffOn hs hn
  · intro i
    exact ((contDiffOn_dot (contDiffOn_gradientAmplitude hU hZ τ (firstDirection i))
      (contDiffOn_gradientAmplitude hU hZ τ (secondDirection i)))).div_const 2
  · intro i
    have ha := weighted_gradientAmplitude hU hτ hs hτs hC hZ hb _ (norm_firstDirection i)
    have hb' := weighted_gradientAmplitude hU hτ hs hτs hC hZ hb _ (norm_secondDirection i)
    have ha' := contDiffOn_gradientAmplitude hU hZ τ (firstDirection i)
    have hb'' := contDiffOn_gradientAmplitude hU hZ τ (secondDirection i)
    have hd := ha.dot hU.uniqueDiffOn hs.le (by positivity) (by positivity) ha' hb'' hb'
    have hh := hd.const_mul hU.uniqueDiffOn (contDiffOn_dot ha' hb'') (1 / 2 : ℂ)
    apply (hh.congr (fun p _ => by dsimp only [doubleTensor]; ring)).mono_const
    simp only [norm_div, norm_one, Complex.norm_ofNat, Fintype.card_fin] at *
    nlinarith

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.dot_real {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : E → ι → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ) * (2 ^ m * C * D))
      (fun x => dotProduct (f x) (g x)) := by
  have hfsm (i : ι) := contDiffOn_pi.mp hf i
  have hgsm (i : ι) := contDiffOn_pi.mp hg i
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2 ^ m * C * D)
    (fun i x => f x i * g x i) (fun i _ => (hfsm i).mul (hgsm i)) (fun i _ =>
      (hbf.component hU hs hC hf i).mul_real hU hs hC hD (hfsm i) (hgsm i)
        (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct] using hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
