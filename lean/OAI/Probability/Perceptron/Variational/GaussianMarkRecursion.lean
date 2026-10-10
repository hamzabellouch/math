import Mathlib
import OAI.Probability.Perceptron.Variational.IntegrableProdConditionalSquare
import OAI.Probability.Perceptron.Variational.EntropicHeat

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_linear_shift {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : E →L[ℝ] E) (a : ℝ) (x : E) :
    Integrable (fun y => Real.exp (a*f (x+A y))) μ := by
  have hA : LipschitzWith ‖A‖₊ (fun y => x+A y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using A.lipschitzWith.dist_le_mul y z
  have hg := hf.comp hA
  simpa using gaussian_integrable_exp_lipschitz μ hg a 1 (0:E)

def gaussianLinearEntropic (b : ℝ) (A : E →L[ℝ] E) (f : E → ℝ) (x : E) : ℝ :=
  entropicMean μ b (fun y => f (x+A y))

lemma gaussianLinearEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {b : ℝ} (hb : 0 ≤ b) (A : E →L[ℝ] E) :
    LipschitzWith L (gaussianLinearEntropic μ b A f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianLinearEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a x)
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a y) hb
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+A z) (y+A z)

def gaussianLinearBackward : List (ℝ×(E →L[ℝ] E)) → (E → ℝ) → E → ℝ
  | [],f => f
  | (b,A)::l,f => gaussianLinearEntropic μ b A (gaussianLinearBackward l f)

lemma gaussianLinearBackward_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (ℝ×(E →L[ℝ] E)))
    (hl : ∀ c ∈ l, 0 ≤ c.1) : LipschitzWith L (gaussianLinearBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons c l ih =>
    exact gaussianLinearEntropic_lipschitz μ
      (ih (fun d hd => hl d (List.mem_cons_of_mem c hd))) (hl c List.mem_cons_self) c.2

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

def gaussianLinearMarkStep (A : ℕ → E →L[ℝ] E) : (ℕ → E)×E → ℕ → E :=
  fun p j => p.1 (j+1)+A j p.2

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

def linearCascadeWord (A : ℕ → E →L[ℝ] E) : (k : ℕ) → (Fin k → ℝ) → List (ℝ×(E →L[ℝ] E))
  | 0,_ => []
  | k+1,z => (z 0,A k)::linearCascadeWord A k (fun i => z i.succ)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_nonneg (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ linearCascadeWord A k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearRecursion_realization (ν : ProbabilityMeasure E) [IsGaussian (ν:Measure E)]
    (A : ℕ → E →L[ℝ] E) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion ν (gaussianLinearMarkStep A) k z (fun x => f (x 0)) x=
        gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k z) f (x k)) ∧
    finiteCascadeFractionalIntegrable ν (gaussianLinearMarkStep A) (fun x => f (x 0)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    let g := gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := gaussianLinearBackward_lipschitz (ν:Measure E) hf _
      (linearCascadeWord_nonneg A k _ (fun i => (hz i.succ).le))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,gaussianLinearMarkStep,
        linearCascadeWord,gaussianLinearBackward,gaussianLinearEntropic]
      rw [entropicMean_eq_div (ν:Measure E)
        (fun a => gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) a (x (k+1)))
        (hz 0).ne']
      rfl
    · constructor
      · intro x
        simp only [H.1,gaussianLinearMarkStep]
        exact gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) (z 0) (x (k+1))
      · exact H.2

end
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianMarkLaw : ProbabilityMeasure E := ⟨stdGaussian E,inferInstance⟩

lemma lipschitz_memLp_stdGaussian {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian E) := by
  have hg : LipschitzWith L (fun x => f x-f 0) := by
    intro x y
    simpa only [edist_sub_right] using hf x y
  have hh := (hg.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))).add
    (memLp_const (f 0))
  convert hh using 1
  ext x
  simp

def gaussianLinearCascadeLog (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    (f : E → ℝ) (k : ℕ) (a : E×DecoratedCascade E k) : ℝ :=
  Real.log (decoratedTerminalTotal (gaussianLinearMarkStep A) (fun x => f (x 0)) k
      ((fun _ => R a.1),a.2) /
    decoratedTerminalTotal (gaussianLinearMarkStep A) (fun _ => 0) k ((fun _ => R a.1),a.2))

lemma gaussianLinearCascadeLog_measurable (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} (hf : Measurable f) (k : ℕ) (z : Fin k → ℝ) :
    Measurable (gaussianLinearCascadeLog A R f k) := by
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  have hm : Measurable (fun a : E×DecoratedCascade E k => ((fun _ : ℕ => R a.1),a.2)) :=
    (Measurable.of_eval (fun _ => R.measurable.comp measurable_fst)).prodMk measurable_snd
  exact (((decoratedTerminalTotal_measurable ν _ (gaussianLinearMarkStep_measurable A)
    (hf.comp (measurable_pi_apply 0)) k z).div
    (decoratedTerminalTotal_measurable ν _ (gaussianLinearMarkStep_measurable A)
      measurable_const k z)).log).comp hm

lemma gaussianLinearCascadeLog_mean (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let ν : ProbabilityMeasure E := gaussianMarkLaw
    let μ := (stdGaussian E).prod (decoratedCascadeLaw ν k z)
    Integrable (gaussianLinearCascadeLog A R f k) μ ∧
      (∫ a, gaussianLinearCascadeLog A R f k a ∂μ)=
        ∫ a, gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)
          ∂stdGaussian E := by
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  let : IsGaussian (ν:Measure E) := (inferInstance : IsGaussian (stdGaussian E))
  let ρ := decoratedCascadeLaw ν k z
  let F := gaussianLinearCascadeLog A R f k
  let G := fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)
  have hr := gaussianLinearRecursion_realization ν A hf k z hz0
  have hmH : Measurable (fun x : ℕ → E => f (x 0)) :=
    hf.continuous.measurable.comp (measurable_pi_apply 0)
  have hG : MemLp G 2 (stdGaussian E) := lipschitz_memLp_stdGaussian
    ((gaussianLinearBackward_lipschitz (stdGaussian E) hf _
      (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le))).comp R.lipschitzWith)
  have hsec (a : E) : MemLp (fun η => F (a,η)) 2 (ρ:Measure _) ∧
      (∫ η, (F (a,η)-G a)^2 ∂ρ) ≤ cascadeLogFluctuationConstant k z := by
    have H := finiteCascade_terminal_log_second_moment_bound ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H
  have hF := gaussianLinearCascadeLog_measurable A R hf.continuous.measurable k z
  have hi : Integrable F ((stdGaussian E).prod ρ) :=
    integrable_prod_of_conditional_square (stdGaussian E) ρ hF hG
      (cascadeLogFluctuationConstant k z) (fun a => (hsec a).1) (fun a => (hsec a).2)
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    have H := finiteCascade_terminal_log_recursion_of_fractional ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H

end SphericalPerceptronFreeEnergy

end

end OAI
