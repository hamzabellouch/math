import Mathlib
import OAI.Probability.Perceptron.Variational.VarianceProdMemLp
import OAI.Probability.Perceptron.Variational.EnrichedMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma memLp_prod_of_conditional_square {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (K : ℝ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ K) : MemLp F 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hF.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable_sq),?_⟩
  have hi : Integrable (fun x => 2*K+2*(G x)^2) μ :=
    (integrable_const _).add (hG.integrable_sq.const_mul 2)
  apply hi.mono' (hF.pow_const 2).aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun y : Y => sq_nonneg (F (x,y))))]
    have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
      ((hs x).sub (memLp_const (G x))).integrable_sq
    calc
      _ ≤ ∫ y, 2*(F (x,y)-G x)^2+2*(G x)^2 ∂ν := by
        apply integral_mono (hs x).integrable_sq ((hi1.const_mul 2).add (integrable_const _))
        intro y
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (F (x,y)-2*G x)]
      _ = 2*(∫ y, (F (x,y)-G x)^2 ∂ν)+2*(G x)^2 := by
        rw [integral_add (hi1.const_mul 2) (integrable_const _),integral_const_mul]
        simp
      _ ≤ _ := by linarith [hb x]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_pos (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0<z i) : ∀ c ∈ linearCascadeWord A k z, 0<c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearCascadeLog_variance (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let ν : ProbabilityMeasure E := gaussianMarkLaw
    let μ := (stdGaussian E).prod (decoratedCascadeLaw ν k z)
    MemLp (gaussianLinearCascadeLog A R f k) 2 μ ∧
      variance (gaussianLinearCascadeLog A R f k) μ ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*((L:ℝ)*‖R‖)^2 := by
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
  have hmean (a : E) : (∫ η, F (a,η) ∂ρ)=G a := by
    have H := finiteCascade_terminal_log_recursion_of_fractional ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H
  have hF := gaussianLinearCascadeLog_measurable A R hf.continuous.measurable k z
  have hp := memLp_prod_of_conditional_square (stdGaussian E) ρ hF hG
    (cascadeLogFluctuationConstant k z) (fun a => (hsec a).1) (fun a => (hsec a).2)
  have hmean' : (fun a => ∫ η, F (a,η) ∂ρ)=G := funext hmean
  refine ⟨hp,?_⟩
  apply variance_prod_le_memLp (stdGaussian E) (ρ:Measure (DecoratedCascade E k))
    (F := F) hp (fun a => (hsec a).1) (hmean'.symm ▸ hG)
  · intro a
    rw [variance_eq_integral (hsec a).1.aestronglyMeasurable.aemeasurable,hmean]
    exact (hsec a).2
  · rw [hmean']
    exact gaussianLinearBackward_root_variance (stdGaussian E) hf hd hD _
      (linearCascadeWord_pos A k z hz0) R
end SphericalPerceptronFreeEnergy
end

end OAI
