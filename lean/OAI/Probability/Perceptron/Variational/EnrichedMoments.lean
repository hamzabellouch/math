import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedDiagonalField

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def enrichedDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    Measure (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) :=
  (stdGaussian (EnrichedMark (n+1) (n+1) p)).prod
    (decoratedCascadeLaw (gaussianMarkLaw : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p)) k z)

instance (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (enrichedDisorderLaw n k p z) := by
  unfold enrichedDisorderLaw
  infer_instance

lemma enrichedCascadeLog_joint_mean (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    Integrable (enrichedCascadeLog n M k f g p d u h) (enrichedDisorderLaw n k p z) ∧
    (∫ a, enrichedCascadeLog n M k f g p d u h a ∂enrichedDisorderLaw n k p z)=
      ∫ a, gaussianLinearBackward (stdGaussian (EnrichedMark (n+1) (n+1) p))
        (linearCascadeWord (enrichedIncrementMap p d h) k z)
        (enrichedTerminal n M f g p u (h (Fin.last k))) (enrichedRootMap p d h a)
        ∂stdGaussian (EnrichedMark (n+1) (n+1) p) := by
  exact gaussianLinearCascadeLog_mean (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _) k z hz hz0 hz1

lemma enrichedCascadeLog_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (enrichedCascadeLog n M k f g p d u h) := by
  exact gaussianLinearCascadeLog_measurable (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _).continuous.measurable k z

lemma enrichedCascadeLog_conditional_square (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (a : EnrichedMark (n+1) (n+1) p) :
    let ν : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p) := gaussianMarkLaw
    let G := gaussianLinearBackward (ν:Measure _) (linearCascadeWord (enrichedIncrementMap p d h) k z)
      (enrichedTerminal n M f g p u (h (Fin.last k))) (enrichedRootMap p d h a)
    MemLp (fun η => enrichedCascadeLog n M k f g p d u h (a,η)) 2
      (decoratedCascadeLaw ν k z : Measure _) ∧
    (∫ η, (enrichedCascadeLog n M k f g p d u h (a,η)-G)^2
      ∂decoratedCascadeLaw ν k z) ≤ cascadeLogFluctuationConstant k z := by
  let ν : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p) := gaussianMarkLaw
  let : IsGaussian (ν:Measure (EnrichedMark (n+1) (n+1) p)) := (inferInstance : IsGaussian (stdGaussian (EnrichedMark (n+1) (n+1) p)))
  have hf := enrichedTerminal_lipschitz n M f g p u (h (Fin.last k))
  have hr := gaussianLinearRecursion_realization ν (enrichedIncrementMap p d h) hf k z hz0
  have H := finiteCascade_terminal_log_second_moment_bound ν
    (gaussianLinearMarkStep (enrichedIncrementMap p d h))
    (gaussianLinearMarkStep_measurable _) k z hz hz0 hz1
    (hf.continuous.measurable.comp (measurable_pi_apply 0)) hr.2
    (fun _ => enrichedRootMap p d h a)
  simp only [Function.comp_def] at H
  rw [hr.1] at H
  exact H

lemma normalizedPatternEnergy_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) (x : NormalizedSpin (n+1)) :
    normalizedPatternEnergy (n+1) (patternCount α (n+1)) (β • φ) g x=
      β*hamiltonian α φ (n+1) g (Real.sqrt (n+1:ℕ) • x.val) := by
  have hn : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have he (a : Fin (patternCount α (n+1))) :
      patternField g a (Real.sqrt (n+1:ℕ) • x.val) = ∑ i, g a i*x.val i := by
    unfold patternField
    simp only [PiLp.smul_apply,smul_eq_mul]
    have hs : (∑ i, g a i*(Real.sqrt (n+1:ℕ)*x.val i)) =
        (∑ i, g a i*x.val i)*Real.sqrt (n+1:ℕ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs,mul_div_cancel_right₀ _ hn]
  simp only [normalizedPatternEnergy,BoundedContinuousFunction.coe_smul,smul_eq_mul,
    hamiltonian,he,Finset.mul_sum]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianLinearEntropic_C1 {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    {b : ℝ} (hb : 0<b) (A : E →L[ℝ] E) :
    ∃ D' : E → StrongDual ℝ E, Continuous D' ∧
      (∀ x, HasFDerivAt (gaussianLinearEntropic μ b A f) (D' x) x) ∧
      (∀ x, ‖D' x‖ ≤ L) := by
  have hfc : Continuous f := hf.continuous
  have hDC (x : E) : ‖D x‖ ≤ L := by
    rw [← (hd x).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  let Z := fun x => ∫ y, Real.exp (b*f (x+A y)) ∂μ
  let ZD := fun x => ∫ y, Real.exp (b*f (x+A y)) • (b • D (x+A y)) ∂μ
  have hZpos (x : E) : 0<Z x := by
    apply integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
      (gaussian_integrable_exp_linear_shift μ hf A b x) |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hdom (x₀ x y : E) (hx : x ∈ Metric.ball x₀ 1) :
      ‖Real.exp (b*f (x+A y)) • (b • D (x+A y))‖ ≤
        (Real.exp (b*L)*(b*L))*Real.exp (b*f (x₀+A y)) := by
    have hh := hf.dist_le_mul (x+A y) (x₀+A y)
    rw [dist_add_right,Real.dist_eq] at hh
    have hx' : dist x x₀ ≤ 1 := (Metric.mem_ball.mp hx).le
    have hff : f (x+A y)-f (x₀+A y) ≤ L :=
      (le_abs_self _).trans (hh.trans (by simpa using mul_le_mul_of_nonneg_left hx' L.coe_nonneg))
    have hExp : Real.exp (b*f (x+A y)) ≤ Real.exp (b*L)*Real.exp (b*f (x₀+A y)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_pos hb]
    calc
      _ ≤ (Real.exp (b*L)*Real.exp (b*f (x₀+A y)))*(b*L) :=
        mul_le_mul hExp (mul_le_mul_of_nonneg_left (hDC _) hb.le) (by positivity) (by positivity)
      _ = _ := by ring
  have hZ (x : E) : HasFDerivAt Z (ZD x) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun x y => Real.exp (b*f (x+A y)) • (b • D (x+A y)))
      (bound := fun y => (Real.exp (b*L)*(b*L))*Real.exp (b*f (x+A y)))
      (Metric.ball_mem_nhds x zero_lt_one)
    · exact Eventually.of_forall fun x => by fun_prop
    · exact gaussian_integrable_exp_linear_shift μ hf A b x
    · fun_prop
    · exact ae_of_all _ fun y x' hx' => hdom x x' y hx'
    · exact (gaussian_integrable_exp_linear_shift μ hf A b x).const_mul _
    · exact ae_of_all _ fun y x' _ => by
        have hh := (hd (x'+A y)).comp x' ((hasFDerivAt_id x').add_const (A y))
        simpa using (hh.const_mul b).exp
  have hZD : Continuous ZD := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply continuousAt_of_dominated
      (bound := fun y => (Real.exp (b*L)*(b*L))*Real.exp (b*f (x+A y)))
    · exact Eventually.of_forall fun x => by fun_prop
    · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with x' hx'
      exact ae_of_all _ fun y => hdom x x' y hx'
    · exact (gaussian_integrable_exp_linear_shift μ hf A b x).const_mul _
    · exact ae_of_all _ fun y => by fun_prop
  let D' := fun x => b⁻¹ • ((Z x)⁻¹ • ZD x)
  have he : gaussianLinearEntropic μ b A f = fun x => Real.log (Z x)/b := by
    funext x
    exact entropicMean_eq_div μ (fun s => gaussian_integrable_exp_linear_shift μ hf A s x) hb.ne'
  have hd' (x : E) : HasFDerivAt (gaussianLinearEntropic μ b A f) (D' x) x := by
    rw [he]
    have hh := ((hZ x).log (hZpos x).ne').const_mul b⁻¹
    simpa only [D',div_eq_mul_inv,mul_comm] using hh
  refine ⟨D',?_,hd',?_⟩
  · have hcZ : Continuous Z := continuous_iff_continuousAt.mpr (fun x => (hZ x).continuousAt)
    change Continuous (fun x => b⁻¹ • ((Z x)⁻¹ • ZD x))
    exact (continuous_const : Continuous (fun _ : E => (b⁻¹ : ℝ))).smul
      ((hcZ.inv₀ (fun x => (hZpos x).ne')).smul hZD)
  · intro x
    rw [← (hd' x).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (gaussianLinearEntropic_lipschitz μ hf hb.le A)

lemma gaussianLinearBackward_C1 {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0<c.1) :
    ∃ D' : E → StrongDual ℝ E, Continuous D' ∧
      (∀ x, HasFDerivAt (gaussianLinearBackward μ l f) (D' x) x) ∧
      (∀ x, ‖D' x‖ ≤ L) := by
  induction l with
  | nil =>
    exact ⟨D,hD,hd,fun x => by
      rw [← (hd x).fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ hf⟩
  | cons c l ih =>
    have hl' : ∀ d ∈ l, 0<d.1 := fun d hd => hl d (List.mem_cons_of_mem c hd)
    obtain ⟨D',hD',hd',_⟩ := ih hl'
    exact gaussianLinearEntropic_C1 μ
      (gaussianLinearBackward_lipschitz μ hf l (fun d hd => (hl' d hd).le))
      hd' hD' (hl c List.mem_cons_self) c.2

lemma gaussianLinearBackward_root_variance {f : E → ℝ} {D : E → StrongDual ℝ E}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x)
    (hD : Continuous D) (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0<c.1)
    (R : E →L[ℝ] E) :
    variance (fun x => gaussianLinearBackward μ l f (R x)) (stdGaussian E) ≤
      (Real.pi^2/8)*((L:ℝ)*‖R‖)^2 := by
  obtain ⟨D',hD',hd',hb⟩ := gaussianLinearBackward_C1 μ hf hd hD l hl
  apply stdGaussian_variance_le_of_fderiv_bound
    (D := fun x => (D' (R x)).comp R)
    (fun x => (hd' (R x)).comp x R.hasFDerivAt)
  · exact Continuous.clm_comp (hD'.comp R.continuous) continuous_const
  · positivity
  · intro x
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg R))

end SphericalPerceptronFreeEnergy

end

end OAI
