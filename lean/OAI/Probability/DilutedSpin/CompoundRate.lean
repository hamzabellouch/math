import OAI.Probability.DilutedSpin.CompoundCoupling
import OAI.Probability.DilutedSpin.CompoundSuperposition
import OAI.Probability.DilutedSpin.InsertionStability
import OAI.Probability.DilutedSpin.NormalizedCutoff

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_id_conv (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) : Integrable id (μ∗ν) := by
  rw [Measure.conv,integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma lipschitz_conv_add_bound (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x, f x ∂(μ∗ν))-(∫ x, f x ∂μ)| ≤ C*(∫ y,‖y‖ ∂ν) := by
  have hfi := integrable_lipschitz_of_id μ hμ hf
  have hfc := integrable_lipschitz_of_id (μ∗ν) (integrable_id_conv μ ν hμ hν) hf
  have hfp : Integrable (fun z : E×E => f (z.1+z.2)) (μ.prod ν) := by
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable (by fun_prop)).mp hfc
  rw [integral_conv hfc,← integral_sub hfp.integral_prod_left hfi]
  calc
    _ ≤ ∫ x, |(∫ y, f (x+y) ∂ν)-f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, (C:ℝ)*(∫ y,‖y‖ ∂ν) ∂μ := by
      apply integral_mono (hfp.integral_prod_left.sub hfi).abs (integrable_const _)
      intro x
      have hx : Integrable (fun y => f (x+y)) ν := by
        apply integrable_lipschitz_of_id ν hν
        simpa only [mul_one,Function.comp_def] using hf.comp (isometry_add_left x).lipschitzWith
      change |(∫ y, f (x+y) ∂ν)-f x|≤_
      have hc : (∫ _y : E, f x ∂ν)=f x := by simp
      rw [← hc,← integral_sub hx (integrable_const _)]
      calc
        _ ≤ ∫ y, |f (x+y)-f x| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ y, (C:ℝ)*‖y‖ ∂ν := by
          apply integral_mono (hx.sub (integrable_const _)).abs (hν.norm.const_mul _)
          intro y
          simpa only [add_sub_cancel_left,Real.norm_eq_abs,Pi.sub_apply,id_eq] using hf.norm_sub_le (x+y) x
        _ = _ := integral_const_mul _ _
    _ = _ := by simp

lemma compoundPoisson_rate_add_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson (r+s) μ)-(∫ x, f x ∂compoundPoisson r μ)| ≤
      C*s*(∫ y,‖y‖ ∂μ) := by
  rw [compoundPoisson_add]
  exact (lipschitz_conv_add_bound _ _ (compoundPoisson_integrable_id r μ hμ)
    (compoundPoisson_integrable_id s μ hμ) hf).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (compoundPoisson_norm_le s μ hμ) C.coe_nonneg)

lemma compoundPoisson_rate_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r μ)-(∫ x, f x ∂compoundPoisson s μ)| ≤
      C*|(r:ℝ)-s| *(∫ y,‖y‖ ∂μ) := by
  rcases le_total s r with h|h
  · have hh := compoundPoisson_rate_add_bound s (r-s) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh
  · have hh := compoundPoisson_rate_add_bound r (s-r) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_sub_comm (∫ x, f x ∂compoundPoisson r μ),abs_sub_comm (r:ℝ),
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal ENNReal BigOperators
variable {Ω I S : Type} [Fintype Ω] [Fintype S]
    {A : I → Type} [∀ i,Fintype (A i)] {L k : ℕ}

lemma root_energy_lipschitz (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ i, 0 < m i) (states : FinitePath Ω L → S)
    (roots : Fin k → I) (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    LipschitzWith 1 (fun E : S → ℝ => root T Q m (fun y => E (states y)) roots factor) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply root_base_stability T Q m hm
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (states y)

lemma root_energy_insertion (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base F : FinitePath Ω L → ℝ)
    (roots : Fin k → I) (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T Q m (base+F) roots factor-root T Q m base roots factor =
      backwardLog L (tilt L (tower roots L T Q) m (logWeight base roots factor)) m
        (fun y => F (physical roots L y)) := by
  unfold root
  rw [← insertion]
  congr 2
  funext y
  simp only [logWeight,Pi.add_apply]
  ring

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory

lemma interaction_clip_symmetric {p : ℕ} (M : Model p) (C : ℝ)
    (hsym : ∀ e : Equiv.Perm (Fin p),IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => (clipSample C z).1)
      (fun z : InteractionSample p => fun s => (clipSample C z).1 (fun i => s (e i)))
      M.disorder.toMeasure M.disorder.toMeasure := by
  exact (hsym e).comp (show Measurable (fun f : (Fin p → Spin) → ℝ => fun s => clipReal C (f s)) from
    Measurable.of_eval (fun spin => (measurable_clipReal C).comp (measurable_pi_apply spin)))

end DilutedSpinGlass

end

end OAI
