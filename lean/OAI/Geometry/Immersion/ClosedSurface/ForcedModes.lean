import OAI.Geometry.Immersion.ClosedSurface.OscillationBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

lemma norm_realPartCLM_le (n : ℕ) : ‖realPartCLM n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Z
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg Z)).2 fun i =>
    ((Complex.abs_re_le_norm (Z i)).trans (norm_le_pi_norm Z i))

def realOsc (τ : ℝ) {n : ℕ} (Z : Field n) : RField n :=
  fun p => QuadraticMean.realPart (oscillate τ Z p)

lemma realOsc_eq_displacement (τ : ℝ) {n : ℕ} (Z : Field n) :
    realOsc τ Z = ClosedSurfaceR4.QuadraticMean.displacement τ Prod.fst Z := by
  funext p
  unfold realOsc ClosedSurfaceR4.QuadraticMean.displacement
    ClosedSurfaceR4.QuadraticMean.realMode oscillate
  congr 2
  simp only [unitMode, ClosedSurfaceR4.QuadraticMean.phase, Complex.ofReal_div]
  congr 1
  ring

lemma contDiffOn_realOsc {n : ℕ} {U : Set Base} {Z : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) : ContDiffOn ℝ ∞ (realOsc τ Z) U :=
  (realPartCLM n).contDiff.comp_contDiffOn (contDiffOn_oscillate hZ τ)

lemma weighted_realPart {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Field n} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => QuadraticMean.realPart (Z p)) := by
  have hh := hb.linear hU hs hZ (realPartCLM n)
  exact hh.mono_const (mul_le_of_le_one_left hC (norm_realPartCLM_le n))

lemma weighted_realOsc {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {τ s C : ℝ} {m : ℕ} {Z : Field n} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U τ m (2 ^ m * C) (realOsc τ Z) :=
  weighted_realPart hU.uniqueDiffOn hτ.le (mul_nonneg (by positivity) hC)
    (contDiffOn_oscillate hZ τ) (weighted_oscillate hU hτ hτs hC hZ hb)

lemma coordDeriv_realPart {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (fun q => QuadraticMean.realPart (Z q)) p = QuadraticMean.realPart (coordDeriv v Z p) := by
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v)
    (((realPartCLM n).hasFDerivAt.comp p hZ.hasFDerivAt).fderiv)

lemma complexify_dot_realPart {n : ℕ} (X : RVec n) (Z : Ambient n) :
    (complexify X ⬝ᵥ Z).re = X ⬝ᵥ QuadraticMean.realPart Z := by
  simp [dotProduct, QuadraticMean.realPart, Complex.mul_re]


def realMetric {n : ℕ} (F : RField n) (v w p : Base) : ℝ :=
  coordDeriv v F p ⬝ᵥ coordDeriv w F p

def realLinearized {n : ℕ} (F U : RField n) (v w p : Base) : ℝ :=
  coordDeriv v F p ⬝ᵥ coordDeriv w U p + coordDeriv w F p ⬝ᵥ coordDeriv v U p

lemma realMetric_add {n : ℕ} {F U : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hU : DifferentiableAt ℝ U p) (v w : Base) :
    realMetric (fun q => F q + U q) v w p =
      realMetric F v w p + realLinearized F U v w p + realMetric U v w p := by
  unfold realMetric realLinearized
  rw [partial_add hF hU v, partial_add hF hU w]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (coordDeriv v U p)]
  ring

lemma realLinearized_realPart {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    realLinearized F (fun q => QuadraticMean.realPart (Z q)) v w p =
      (linearizedMetric (fun q => complexify (F q)) Z v w p).re := by
  simp only [realLinearized, linearizedMetric, coordDeriv_realPart hZ,
    coordDeriv_complexify hF, Complex.add_re, complexify_dot_realPart]

lemma realLinearized_realOsc {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v w : Base) :
    realLinearized F (realOsc τ Z) v w p =
      (unitMode τ p * conjugatedMetric τ (fun q => complexify (F q)) Z v w p).re := by
  have hO : DifferentiableAt ℝ (oscillate τ Z) p := by
    unfold oscillate
    exact (unitMode_hasFDerivAt τ p).differentiableAt.smul hZ
  unfold realOsc
  rw [realLinearized_realPart hF hO, linearizedMetric_oscillate τ hZ]

def realMetricTensor {n : ℕ} (F : RField n) : Base → Fin 3 → ℝ :=
  fun p => ![realMetric F dx dx p, realMetric F dx dy p, realMetric F dy dy p]

def realLinearizedTensor {n : ℕ} (F U : RField n) : Base → Fin 3 → ℝ :=
  fun p => ![realLinearized F U dx dx p, realLinearized F U dx dy p,
    realLinearized F U dy dy p]

lemma realLinearized_residual {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (f : Tensor) :
    realLinearizedTensor F (realOsc τ Z) p - realOsc τ f p =
      realOsc τ (SmallModes.residual τ (fun q => complexify (F q)) f Z) p := by
  ext i
  fin_cases i <;>
    simp [realLinearizedTensor, realLinearized_realOsc hF hZ, realOsc, QuadraticMean.realPart,
      oscillate, SmallModes.residual, conjugatedD, tensorOf, mul_sub, Matrix.vecHead, Matrix.vecTail]




theorem real_finite_forced_mode {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (h : ModeDomain (fun p => complexify (F p)) U)
    {τ s K C : ℝ} {f : SmallModes.Tensor} (hτ : 0 < τ) (hs : 0 < s)
    (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f) :
    let Z := modeApprox τ (fun p => complexify (F p)) (fun _ => 0) f q
    ContDiffOn ℝ ∞ (realOsc τ Z) U ∧
    WeightedBound U τ m (2 ^ m * (forcedModeConstant n m K q * C)) (realOsc τ Z) ∧
    WeightedBound U τ m
      (2 ^ m * (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C))
      (fun p => realLinearizedTensor F (realOsc τ Z) p - realOsc τ f p) := by
  dsimp only
  have hm := contDiffOn_modeApprox τ h (V := fun _ => 0) contDiffOn_const hf q
  have hz : WeightedBound U s (m + q + 1) C (fun _ : Base => (0 : Ambient n)) :=
    (weightedBound_zero U s _).mono_const hC
  have hX : ∀ p ∈ U, coordDeriv dx (fun p => complexify (F p)) p ⬝ᵥ (0 : Ambient n) = 0 := by
    intro p hp; simp
  have hY : ∀ p ∈ U, coordDeriv dy (fun p => complexify (F p)) p ⬝ᵥ (0 : Ambient n) = 0 := by
    intro p hp; simp
  have hV : ∀ p ∈ U, goodSecond (fun p => complexify (F p)) p ⬝ᵥ (0 : Ambient n) = 0 := by
    intro p hp; simp
  have ha := weighted_modeApprox hτ (contDiff_complexify hF) h hs hτs hs1 hK hC
    hf (V := fun _ => 0) contDiffOn_const hX hY hV q m hc hb hz
  have hr := weighted_residual_modeApprox hτ (contDiff_complexify hF) h hs hs1 hK hC
    hf (V := fun _ => 0) contDiffOn_const hX hY hV q m hc.toFullModeCoefficientBound hb hz
  refine ⟨contDiffOn_realOsc hm τ, weighted_realOsc h.isOpen hτ hτs
    (mul_nonneg (forcedModeConstant_nonneg n m q hK) hC) hm ha, ?_⟩
  have hsmooth := contDiffOn_residual τ h hm hf
  have hn : 0 ≤ fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C :=
    mul_nonneg (mul_nonneg (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)
      (pow_nonneg (div_nonneg hτ.le hs.le) _)) hC
  have hr' := weighted_realOsc h.isOpen hτ hτs hn hsmooth hr
  apply hr'.congr
  intro p hp
  exact realLinearized_residual (hF.differentiable (by simp) p)
    (((hm p hp).contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by simp)) τ f

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.WeightedEstimates

lemma WeightedBound.enlarge_scale {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {s C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hC : 0 ≤ C) {c : ℝ} (hc : 1 ≤ c) :
    WeightedBound U (c * s) m (c ^ m * C) f := by
  intro j hj p hp
  calc
    _ = c ^ j * (s ^ j * ‖iteratedFDerivWithin ℝ j f U p‖) := by rw [mul_pow]; ring
    _ ≤ c ^ j * C := mul_le_mul_of_nonneg_left (h j hj p hp) (pow_nonneg (by linarith) _)
    _ ≤ c ^ m * C := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hj) hC

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
